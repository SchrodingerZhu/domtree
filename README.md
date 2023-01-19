# domtree

`domtree` provides facilities a generic implementation to calculate the dominator tree of
a directed graph. The algorithm basically follows the description in
"A Simple, Fast Dominance Algorithm" by Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy.
To implement the trait for your own graph structure, you need to prepare several fields:
```rust
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
impl<T : PartialEq + Eq + Hash> MemberSet<T> for HashMemberSet<T>  {
    fn contains(&self, target: T) -> bool {
        self.0.contains(&target)
    }
    fn insert(&mut self, target: T) {
        self.0.insert(target);
    }
}
#[derive(Debug)]
struct Node {
    tag: usize,                                  // node's identifier
    dom: Option<usize>,                          // node's immediate dominator
    frontiers: UnsafeCell<HashMemberSet<usize>>, // node's dominance frontiers
    incoming_edges: Vec<usize>,                  // node's in-edges
    outgoing_edges: Vec<usize>                   // node's out-edges
}
#[derive(Debug)]
struct Graph {
    nodes: Vec<Node>,
}
```
Then, one needs to first expose some APIs such that this crate can run DFS on the graph.
```rust
use std::iter::Cloned;
use std::slice::Iter;
use domtree::dfs::DFSGraph;
impl DFSGraph for Graph {
    type Identifier = usize;
    type Set<Y> = VecSet<Y>  where Y: Clone + Default;
    type SuccessorIter<'a> = Cloned<Iter<'a, usize>> where Self: 'a;
    fn create_set<Y>(&self) -> Self::Set<Y> where Y: Clone + Default {
        let mut data = Vec::new();
        data.resize(self.nodes.len(), Default::default());
        VecSet(data)
    }
    fn outgoing_edges<'a>(&'a self, id: Self::Identifier) -> Self::SuccessorIter<'a> {
        self.nodes[id].outgoing_edges.iter().cloned()
    }
}
```
After this, one also need to specify how the algorithm can access the fields related to the
dominance tree.
```rust
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
        self.nodes.iter_mut().map(|x|&mut x.dom)
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
```
Then, one can just run populate the dominance tree and the dominance frontiers
```rust
let mut g = random_graph(10000);
dump_graph(&g);
g.populate_dom(0);
g.populate_frontiers();
```