use crate::dfs::DFSGraph;
use crate::djgraph::{DJGraph, MaterializedIDF};
use crate::set::{AssocSet, MemberSet, MergeSet};
use crate::{frontier::DominanceFrontier, DomTree};
use rand::{thread_rng, Rng};
use std::cell::UnsafeCell;
use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;
use std::iter::{Cloned, Map};
use std::ops::Range;
use std::slice::{Iter, IterMut};

#[derive(Clone)]
struct VecSet<Y>(Vec<Y>);

impl<Y: Clone + Default> AssocSet<usize, Y> for VecSet<Y> {
    fn get(&self, target: usize) -> Y {
        self.0[target].clone()
    }

    fn set(&mut self, key: usize, val: Y) {
        self.0[key] = val;
    }
}

#[derive(Clone, Debug, Default)]
struct HashMemberSet<T>(HashSet<T>);

impl<T: PartialEq + Eq + Hash + Clone> MemberSet<T> for HashMemberSet<T> {
    fn contains(&self, target: T) -> bool {
        self.0.contains(&target)
    }

    fn insert(&mut self, target: T) {
        self.0.insert(target);
    }

    type MemberIter<'a> = Cloned<std::collections::hash_set::Iter<'a, T>> where Self : 'a;

    fn iter<'a>(&'a self) -> Self::MemberIter<'a> {
        self.0.iter().cloned()
    }
}

impl<T: PartialEq + Eq + Hash + Clone> MergeSet<T> for HashMemberSet<T> {
    fn subset(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    fn union(&mut self, other: &Self) {
        for i in other.0.iter().cloned() {
            self.0.insert(i);
        }
    }
}

impl MaterializedIDF for Graph {
    type MergeNodeSet = HashMemberSet<usize>;

    fn idf_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::MergeNodeSet> {
        &self.nodes[id].idfs
    }
}

#[derive(Debug)]
struct Node {
    tag: usize,
    dom: Option<usize>,
    frontiers: UnsafeCell<HashMemberSet<usize>>,
    j_edges: UnsafeCell<HashMemberSet<usize>>,
    d_edges: UnsafeCell<HashMemberSet<usize>>,
    idfs: UnsafeCell<HashMemberSet<usize>>,
    incoming_edges: Vec<usize>,
    outgoing_edges: Vec<usize>,
}

#[derive(Debug)]
struct Graph {
    nodes: Vec<Node>,
}

impl Graph {
    fn new(n: usize) -> Self {
        let mut nodes = Vec::new();
        for i in 0..n {
            nodes.push(Node {
                tag: i,
                dom: None,
                frontiers: HashMemberSet(HashSet::new()).into(),
                incoming_edges: Vec::new(),
                outgoing_edges: Vec::new(),
                d_edges: HashMemberSet(HashSet::new()).into(),
                j_edges: HashMemberSet(HashSet::new()).into(),
                idfs: HashMemberSet(HashSet::new()).into(),
            })
        }
        Self { nodes }
    }

    fn iterate_df(&self, set: &HashMemberSet<usize>) -> HashMemberSet<usize> {
        let mut closure = HashMemberSet(HashSet::new());
        let mut changed = true;
        for i in set.iter() {
            for j in self.frontiers(i).iter() {
                closure.insert(j);
            }
        }
        while changed {
            changed = false;
            let mut change_set = Vec::new();
            for i in closure.iter() {
                for j in self.frontiers(i).iter() {
                    if !closure.contains(j) {
                        changed = true;
                        change_set.push(j);
                    }
                }
            }
            for i in change_set {
                closure.insert(i)
            }
        }
        return closure;
    }

    fn connect(&mut self, x: usize, y: usize) {
        self.nodes[x].outgoing_edges.push(y);
        self.nodes[y].incoming_edges.push(x);
    }
}

impl DFSGraph for Graph {
    type Identifier = usize;
    type Set<Y> = VecSet<Y>  where Y: Clone + Default;
    type SuccessorIter<'a> = Cloned<Iter<'a, usize>> where Self: 'a;

    fn create_set<Y>(&self) -> Self::Set<Y>
    where
        Y: Clone + Default,
    {
        let mut data = Vec::new();
        data.resize(self.nodes.len(), Default::default());
        VecSet(data)
    }

    fn outgoing_edges<'a>(&'a self, id: Self::Identifier) -> Self::SuccessorIter<'a> {
        self.nodes[id].outgoing_edges.iter().cloned()
    }
}

impl DomTree for Graph {
    type MutDomIter<'a> = Map<IterMut<'a, Node>, fn(&'a mut Node)->&'a mut Option<usize>> where Self: 'a;
    type PredecessorIter<'a> = Cloned<Iter<'a, usize>> where Self: 'a;

    fn dom(&self, id: Self::Identifier) -> Option<Self::Identifier> {
        self.nodes[id].dom.clone()
    }

    fn set_dom(&mut self, id: Self::Identifier, target: Option<Self::Identifier>) {
        self.nodes[id].dom = target;
    }

    fn predecessor_iter<'a>(&'a self, id: Self::Identifier) -> Self::PredecessorIter<'a> {
        self.nodes[id].incoming_edges.iter().cloned()
    }

    fn doms_mut<'a>(&'a mut self) -> Self::MutDomIter<'a> {
        self.nodes.iter_mut().map(|x| &mut x.dom)
    }
}

impl DJGraph for Graph {
    type NodeSet = HashMemberSet<Self::Identifier>;
    type NodeIter<'a> = Map<Iter<'a, Node>, fn(&'a Node)->usize> where Self: 'a;

    fn create_node_set(&self) -> Self::NodeSet {
        HashMemberSet(HashSet::new())
    }

    fn node_iter<'a>(&'a self) -> Self::NodeIter<'a> {
        self.nodes.iter().map(|x| x.tag)
    }

    fn d_edge_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::NodeSet> {
        &self.nodes[id].d_edges
    }

    fn j_edge_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::NodeSet> {
        &self.nodes[id].j_edges
    }
}

impl DominanceFrontier for Graph {
    type FrontierSet = HashMemberSet<usize>;
    type NodeIter<'a> = Range<usize> where Self: 'a ;

    fn frontiers_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::FrontierSet> {
        &self.nodes[id].frontiers
    }

    fn node_iter<'a>(&'a self) -> Self::NodeIter<'a> {
        0..self.nodes.len()
    }
}

impl Graph {
    fn brutal_force_dom(&self) -> Vec<BTreeSet<usize>> {
        let post_order = self.post_order_sequence(0);
        let mut dominators = Vec::new();
        dominators.resize(self.nodes.len(), BTreeSet::new());
        for i in dominators.iter_mut() {
            for j in 0..self.nodes.len() {
                i.insert(j);
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            for i in post_order.iter().rev().cloned() {
                let next = self.nodes[i]
                    .incoming_edges
                    .iter()
                    .map(|x| dominators[*x].clone())
                    .next()
                    .unwrap_or(BTreeSet::new());
                let mut next = self.nodes[i]
                    .incoming_edges
                    .iter()
                    .skip(1)
                    .fold(next, |acc, x| {
                        dominators[*x].intersection(&acc).cloned().collect()
                    });
                next.insert(i);
                if next != dominators[i] {
                    changed = true;
                    dominators[i] = next;
                }
            }
        }

        dominators
    }
}

fn random_graph<R: Rng>(rng: &mut R, n: usize) -> Graph {
    let mut g = Graph::new(n);
    let mut edges = HashSet::new();
    for i in 0..n - 1 {
        g.connect(i, i + 1);
        edges.insert((i, i + 1));
    }

    for _ in 0..(n / 2) {
        let x = rng.next_u64() as usize % n;
        let y = rng.next_u64() as usize % n;
        if !edges.contains(&(x, y)) && y != 0 {
            edges.insert((x, y));
            g.connect(x, y);
        }
    }
    g
}

fn dump_graph(g: &Graph) {
    println!("digraph G {{");
    for i in g.nodes.iter() {
        for j in i.outgoing_edges.iter() {
            println!("\t{} -> {};", i.tag, j)
        }
    }
    println!("}}");
}

fn dump_dom(g: &Graph) {
    println!("digraph G {{");
    for i in g.nodes.iter() {
        for j in g.d_edge_iter(i.tag) {
            println!("\t{} -> {};", i.tag, j);
        }
        for j in g.j_edge_iter(i.tag) {
            println!("\t{} -> {} [style=\"dashed\"];", i.tag, j);
        }
    }
    println!("}}");
}

#[test]
fn test_dom_tree_calculation() {
    let mut g = random_graph(&mut thread_rng(), 2000);
    dump_graph(&g);
    g.populate_dom(0);

    let doms = g.brutal_force_dom();
    for (idx, i) in doms.iter().cloned().enumerate() {
        let x = i.iter().cloned().collect::<Vec<_>>();
        let mut y = g.dom_iter(idx).collect::<Vec<_>>();
        y.push(idx);
        y.sort();
        assert_eq!(x, y, "failed to match for idx: {}", idx);
    }
}

#[test]
fn test_frontiers_calculation() {
    let mut g = random_graph(&mut thread_rng(), 10000);
    dump_graph(&g);
    g.populate_dom(0);
    g.populate_frontiers();
    for i in g.nodes.iter() {
        for j in g.frontiers(i.tag).0.iter() {
            assert!(!g.dom_iter(*j).any(|x| x == i.tag));
            assert!(
                g.predecessor_iter(*j)
                    .any(|p| i.tag == p || g.dom_iter(p).any(|x| x == i.tag)),
                "failed to match for pair: {}, {}",
                i.tag,
                j
            )
        }
    }
}

#[test]
fn test_frontiers_with_dj_graph() {
    let mut g = random_graph(&mut thread_rng(), 10000);
    dump_graph(&g);
    g.populate_dom(0);
    g.populate_frontiers();
    g.populate_d_edges();
    g.populate_j_edges();
    let depths = g.dom_dfs_depths(0);
    for i in g.nodes.iter() {
        let mut x: Vec<usize> = g.dj_dom_frontiers(&depths, i.tag).iter().collect();
        x.sort();
        let mut y: Vec<usize> = g.frontiers(i.tag).iter().collect();
        y.sort();
        assert_eq!(x, y, "node: {}", i.tag);
    }
}

#[test]
fn test_iterated_frontiers() {
    let mut g = random_graph(&mut thread_rng(), 10000);
    dump_graph(&g);
    g.populate_dom(0);
    g.populate_frontiers();
    g.populate_d_edges();
    g.populate_j_edges();
    let depths = g.dom_dfs_depths(0);
    let indices = rand::seq::index::sample(&mut rand::thread_rng(), g.nodes.len(), 2000);
    let set = HashMemberSet(indices.iter().collect());
    let x = g.iterate_df(&set);
    let y = g.iterated_frontiers(&depths, &set);
    assert_eq!(x.0, y.0);
}

#[test]
fn test_materialized_iterated_frontiers() {
    let mut g = random_graph(&mut thread_rng(), 500);
    dump_graph(&g);
    g.populate_dom(0);
    g.populate_frontiers();
    g.populate_d_edges();
    g.populate_j_edges();
    g.populate_idf(0);
    let depths = g.dom_dfs_depths(0);
    for i in g.nodes.iter() {
        let x = g.iterated_frontiers(&depths, &HashMemberSet([i.tag].into()));
        assert_eq!(x.0, g.ref_idf(i.tag).0, "node: {}", i.tag);
    }
}

#[test]
fn test_example() {
    let mut g = Graph::new(12);
    g.connect(0, 1);
    g.connect(1, 2);
    g.connect(2, 3);
    g.connect(2, 11);
    g.connect(3, 4);
    g.connect(3, 8);
    g.connect(4, 5);
    g.connect(5, 6);
    g.connect(6, 5);
    g.connect(6, 7);
    g.connect(7, 2);
    g.connect(8, 9);
    g.connect(9, 6);
    g.connect(9, 10);
    g.connect(10, 8);
    g.populate_dom(0);
    g.populate_d_edges();
    g.populate_j_edges();
    dump_dom(&g);
    let depths = g.dom_dfs_depths(0);
    let df = g.iterated_frontiers(&depths, &HashMemberSet([1, 3, 4, 7].into_iter().collect()));
    assert_eq!(df.0, [2, 5, 6].into());
}
