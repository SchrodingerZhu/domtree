use crate::dfs::DFSGraph;
use crate::set::{AssocSet, MemberSet};
use crate::{DomTree, DominanceFrontier};
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

#[derive(Clone, Debug)]
struct HashMemberSet<T>(HashSet<T>);

impl<T: PartialEq + Eq + Hash> MemberSet<T> for HashMemberSet<T> {
    fn contains(&self, target: T) -> bool {
        self.0.contains(&target)
    }

    fn insert(&mut self, target: T) {
        self.0.insert(target);
    }
}

#[derive(Debug)]
struct Node {
    tag: usize,
    dom: Option<usize>,
    frontiers: UnsafeCell<HashMemberSet<usize>>,
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
            })
        }
        Self { nodes }
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

fn random_graph(n: usize) -> Graph {
    use rand::*;
    let mut rng = thread_rng();
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

#[test]
fn test_dom_tree_calculation() {
    let mut g = random_graph(2000);
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
    let mut g = random_graph(10000);
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
