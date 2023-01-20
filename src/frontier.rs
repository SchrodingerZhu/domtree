use std::cell::UnsafeCell;

use crate::set::MemberSet;
use crate::DomTree;

/// Interfaces related to dominance frontier calculation
pub trait DominanceFrontier: DomTree {
    /// [`Self::FrontierSet`] is used to maintain the dominance frontier.
    /// Each node should hold a separate [`Self::FrontierSet`].
    type FrontierSet: MemberSet<Self::Identifier>;
    /// [`Self::NodeIter`] is an iterator over all nodes of the graph.
    type NodeIter<'a>: Iterator<Item = Self::Identifier>
    where
        Self: 'a;
    /// Due to mutable reference limitations, the trait expects [`Self::FrontierSet`] to
    /// be wrapped in a [`UnsafeCell`] to allow iterated update. This method is used to
    /// access the [`UnsafeCell`].
    fn frontiers_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::FrontierSet>;
    /// A helper function that is auto derived for user to access the dominance frontiers of
    /// the given node.
    fn frontiers(&self, id: Self::Identifier) -> &Self::FrontierSet {
        unsafe { &*self.frontiers_cell(id).get() }
    }
    /// Gets an iterator over all nodes of the graph.
    fn node_iter<'a>(&'a self) -> Self::NodeIter<'a>;

    /// Calculate the dominance frontiers of all nodes. The immediate dominators must be
    /// calculated before calling this function. Otherwise, it will not crash but the answers can get
    /// wrong.
    fn populate_frontiers(&mut self) {
        for i in self.node_iter() {
            for mut p in self.predecessor_iter(i) {
                if let Some(dom) = self.dom(i) {
                    while p != dom {
                        unsafe {
                            (*self.frontiers_cell(p).get()).insert(i);
                        }
                        if let Some(pdom) = self.dom(p) {
                            p = pdom;
                        } else {
                            break;
                        }
                    }
                }
            }
        }
    }
}
