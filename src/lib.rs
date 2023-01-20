//! `domtree` provides facilities a generic implementation to calculate the dominator tree of
//! a directed graph. The algorithm basically follows the description in
//! "A Simple, Fast Dominance Algorithm" by Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy.
//!
//! To implement the trait for your own graph structure, you need to prepare several fields:
//! ```ignore
//! #[derive(Clone)]
//! struct VecSet<Y>(Vec<Y>);
//!
//! impl<Y: Clone + Default> AssocSet<usize, Y> for VecSet<Y> {
//!     fn get(&self, target: usize) -> Y {
//!         self.0[target].clone()
//!     }
//!
//!     fn set(&mut self, key: usize, val: Y) {
//!         self.0[key] = val;
//!     }
//! }
//!
//! #[derive(Clone, Debug)]
//! struct HashMemberSet<T>(HashSet<T>);
//! impl<T : PartialEq + Eq + Hash> MemberSet<T> for HashMemberSet<T>  {
//!     fn contains(&self, target: T) -> bool {
//!         self.0.contains(&target)
//!     }
//!
//!     fn insert(&mut self, target: T) {
//!         self.0.insert(target);
//!     }
//! }
//!
//! #[derive(Debug)]
//! struct Node {
//!     tag: usize,                                  // node's identifier
//!     dom: Option<usize>,                          // node's immediate dominator
//!     frontiers: UnsafeCell<HashMemberSet<usize>>, // node's dominance frontiers
//!     incoming_edges: Vec<usize>,                  // node's in-edges
//!     outgoing_edges: Vec<usize>                   // node's out-edges
//! }
//!
//! #[derive(Debug)]
//! struct Graph {
//!     nodes: Vec<Node>,
//! }
//! ```
//! Then, one needs to first expose some APIs such that this crate can run DFS on the graph.
//! ```ignore
//! use std::iter::Cloned;
//! use std::slice::Iter;
//! use domtree::dfs::DFSGraph;
//! impl DFSGraph for Graph {
//!     type Identifier = usize;
//!     type Set<Y> = VecSet<Y>  where Y: Clone + Default;
//!     type SuccessorIter<'a> = Cloned<Iter<'a, usize>> where Self: 'a;
//!
//!     fn create_set<Y>(&self) -> Self::Set<Y> where Y: Clone + Default {
//!         let mut data = Vec::new();
//!         data.resize(self.nodes.len(), Default::default());
//!         VecSet(data)
//!     }
//!
//!     fn outgoing_edges<'a>(&'a self, id: Self::Identifier) -> Self::SuccessorIter<'a> {
//!         self.nodes[id].outgoing_edges.iter().cloned()
//!     }
//! }
//! ```
//! After this, one also need to specify how the algorithm can access the fields related to the
//! dominance tree.
//! ```ignore
//! impl DomTree for Graph {
//!     type MutDomIter<'a> = Map<IterMut<'a, Node>, fn(&'a mut Node)->&'a mut Option<usize>> where Self: 'a;
//!     type PredecessorIter<'a> = Cloned<Iter<'a, usize>> where Self: 'a;
//!
//!     fn dom(&self, id: Self::Identifier) -> Option<Self::Identifier> {
//!         self.nodes[id].dom.clone()
//!     }
//!
//!     fn set_dom(&mut self, id: Self::Identifier, target: Option<Self::Identifier>) {
//!         self.nodes[id].dom = target;
//!     }
//!
//!     fn predecessor_iter<'a>(&'a self, id: Self::Identifier) -> Self::PredecessorIter<'a> {
//!         self.nodes[id].incoming_edges.iter().cloned()
//!     }
//!
//!     fn doms_mut<'a>(&'a mut self) -> Self::MutDomIter<'a> {
//!         self.nodes.iter_mut().map(|x|&mut x.dom)
//!     }
//! }
//!
//! impl DominanceFrontier for Graph {
//!     type FrontierSet = HashMemberSet<usize>;
//!     type NodeIter<'a> = Range<usize> where Self: 'a ;
//!
//!     fn frontiers_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::FrontierSet> {
//!         &self.nodes[id].frontiers
//!     }
//!
//!     fn node_iter<'a>(&'a self) -> Self::NodeIter<'a> {
//!         0..self.nodes.len()
//!     }
//! }
//! ```
//! Then, one can just run populate the dominance tree and the dominance frontiers
//! ```ignore
//! let mut g = random_graph(10000);
//! dump_graph(&g);
//! g.populate_dom(0);
//! g.populate_frontiers();
//! ```
use crate::dfs::DFSGraph;
use crate::set::AssocSet;

/// DFS related interfaces.
pub mod dfs;
/// Domaination frontiers
pub mod frontier;
/// Housekeeping data structure interfaces.
pub mod set;

#[cfg(test)]
mod test;

/// An iterator over the dominators of a given node.
pub struct DominatorIter<'a, T: DomTree> {
    tree: &'a T,
    current: T::Identifier,
}

impl<'a, T: DomTree> Iterator for DominatorIter<'a, T> {
    type Item = T::Identifier;
    fn next(&mut self) -> Option<Self::Item> {
        let dom = self.tree.dom(self.current).filter(|x| *x != self.current);
        if let Some(x) = dom {
            self.current = x;
        }
        dom
    }
}

/// Interfaces related to Dominance Tree construction.
pub trait DomTree: DFSGraph + Sized {
    /// [`Self::MutDomIter`] is used in [`Self::doms_mut`] to get an iterator
    /// over all nodes and return the mutable references to their immediate dominator identifiers.
    type MutDomIter<'a>: Iterator<Item = &'a mut Option<Self::Identifier>>
    where
        Self: 'a;
    /// [`Self::PredecessorIter`] is similiar to [`DFSGraph::SuccessorIter`], but it returns
    /// incoming edges instead.
    type PredecessorIter<'a>: Iterator<Item = Self::Identifier>
    where
        Self: 'a;

    /// Returns the identifier of the immediate dominator of the given node.
    fn dom(&self, id: Self::Identifier) -> Option<Self::Identifier>;
    /// Updates the immediate dominator identifier of the given node.
    fn set_dom(&mut self, id: Self::Identifier, target: Option<Self::Identifier>);
    /// Returns an iterator over the incoming edges of the given node.
    fn predecessor_iter<'a>(&'a self, id: Self::Identifier) -> Self::PredecessorIter<'a>;
    /// Returns an iterator over all nodes which yields the mutable references to their immediate
    /// dominator identifiers.
    fn doms_mut<'a>(&'a mut self) -> Self::MutDomIter<'a>;
    /// Returns an iterator over all the **strict** dominators of a node.
    fn dom_iter(&self, id: Self::Identifier) -> DominatorIter<Self> {
        DominatorIter {
            tree: self,
            current: id,
        }
    }
    /// Calculate all the immediate dominator for all nodes. This will form the dominator tree.
    fn populate_dom(&mut self, root: Self::Identifier) {
        // two-pointer algorithm to trace LCA.
        fn intersect<D: DomTree>(
            tree: &D,
            order_map: &D::Set<usize>,
            mut x: D::Identifier,
            mut y: D::Identifier,
        ) -> D::Identifier {
            unsafe {
                while x != y {
                    while order_map.get(x) < order_map.get(y) {
                        // safe because we are processing in reverse post order.
                        x = tree.dom(x).unwrap_unchecked();
                    }
                    while order_map.get(y) < order_map.get(x) {
                        // safe because we are processing in reverse post order.
                        y = tree.dom(y).unwrap_unchecked();
                    }
                }
            }
            return x;
        }
        // initialize all immediate dominators to None.
        self.doms_mut().for_each(|x| *x = None);
        // set root to be its own immediate dominator.
        self.set_dom(root, Some(root));

        // establish post oder using DFS.
        let post_order = self.post_order_sequence(root);
        let mut post_order_map = self.create_set();
        for (i, k) in post_order.iter().cloned().enumerate() {
            post_order_map.set(k, i);
        }

        // Iterate until the fixed point is reached.
        let mut changed = true;
        while changed {
            changed = false;
            for (order, i) in post_order.iter().cloned().enumerate().rev() {
                if i == root {
                    continue;
                }
                let dom = unsafe {
                    self.predecessor_iter(i)
                        .filter(|x| post_order_map.get(*x) > order)
                        .next()
                        // safe because we are processing in reverse post order.
                        .unwrap_unchecked()
                };
                let dom = self
                    .predecessor_iter(i)
                    .filter(|x| *x != dom && self.dom(*x).is_some())
                    .fold(dom, |dom, x| intersect(self, &post_order_map, x, dom));

                if self.dom(i).map(|x| x != dom).unwrap_or(true) {
                    self.set_dom(i, Some(dom));
                    changed = true;
                }
            }
        }
    }
}
