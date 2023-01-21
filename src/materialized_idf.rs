use crate::djgraph::DJGraph;
use crate::set::AssocSet;
use crate::set::MemberSet;
use crate::set::MergeSet;
use std::cell::UnsafeCell;
use std::collections::{HashSet, VecDeque};
use std::hash::Hash;
/// A DJGraph where the iterated dominance frontiers can be materialized.
pub trait MaterializedIDF: DJGraph<Identifier: Hash> {
    /// A [`MergeSet`] used to maintain iterated DF.
    type MergeNodeSet: MergeSet<Self::Identifier>;
    /// Returns the reference to IDF storage
    fn idf_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::MergeNodeSet>;
    /// A helper function to access idfs
    fn ref_idf<'a>(&'a self, id: Self::Identifier) -> &Self::MergeNodeSet {
        unsafe { &(*self.idf_cell(id).get()) }
    }
    /// Returns the BFS order of the DJGraph
    fn bfs_order(&self, root: Self::Identifier) -> Vec<Self::Identifier> {
        let mut queue = VecDeque::new();
        let mut result = Vec::new();
        let mut visited = self.create_set();
        queue.push_back(root);
        visited.set(root, true);
        while let Some(x) = queue.pop_front() {
            result.push(x);
            for i in self.d_edge_iter(x) {
                if !visited.get(i) {
                    visited.set(i, true);
                    queue.push_back(i);
                }
            }
        }
        result
    }
    /// Calculate the IDFs for all nodes. Better call [`DJGraph::populate_d_edges`] first.
    /// At each node, this should give the same result of [`DJGraph::iterated_frontiers`]. However,
    /// this method calculate all nodes in one batch. Notice that this method may not be faster than
    /// calling [`DJGraph::iterated_frontiers`] for each node based on the performance of
    /// underlying the [`MergeSet`] implementation.
    fn populate_idf(&mut self, root: Self::Identifier) {
        fn tdmsc<G: MaterializedIDF>(
            graph: &G,
            bfs_order: &Vec<G::Identifier>,
            depths: &G::Set<usize>,
            hint: Option<usize>,
        ) -> (bool, usize) {
            let mut visited = HashSet::new();
            if let Some(hint) = hint {
                visited.reserve(hint);
            }
            let mut unfinished = false;
            for z in bfs_order.iter().cloned() {
                for e in graph
                    .predecessor_iter(z)
                    .filter(|e| graph.dom(z).map(|p| p != *e).unwrap_or(false))
                {
                    if !visited.contains(&(e, z)) {
                        visited.insert((e, z));
                        let mut x = e;
                        let mut last_x = None;
                        while depths.get(x) >= depths.get(z) {
                            unsafe {
                                (*graph.idf_cell(x).get()).union(&*graph.idf_cell(z).get());
                                (*graph.idf_cell(x).get()).insert(z);
                            }
                            last_x.replace(x);
                            if let Some(p) = graph.dom(x).filter(|p| *p != x) {
                                x = p;
                            } else {
                                break;
                            }
                        }
                        if let Some(last_x) = last_x {
                            for i in graph
                                .predecessor_iter(last_x)
                                .filter(|e| graph.dom(last_x).map(|p| p != *e).unwrap_or(false))
                            {
                                if visited.contains(&(i, last_x))
                                    && unsafe {
                                        !(*graph.idf_cell(last_x).get())
                                            .subset(&*graph.idf_cell(i).get())
                                    }
                                {
                                    let mut y = i;
                                    let mut last_y = None;
                                    while depths.get(y) >= depths.get(last_x) {
                                        unsafe {
                                            (*graph.idf_cell(y).get())
                                                .union(&*graph.idf_cell(last_x).get());
                                        }
                                        last_y.replace(y);
                                        if let Some(p) = graph.dom(y).filter(|p| *p != x) {
                                            y = p;
                                        } else {
                                            break;
                                        }
                                    }
                                    if last_y
                                        .map(|last_y| {
                                            graph
                                                .predecessor_iter(last_y)
                                                .filter(|e| {
                                                    graph
                                                        .dom(last_y)
                                                        .map(|p| p != *e)
                                                        .unwrap_or(false)
                                                })
                                                .any(|p| unsafe {
                                                    !(*graph.idf_cell(last_y).get())
                                                        .subset(&*graph.idf_cell(p).get())
                                                })
                                        })
                                        .unwrap_or(false)
                                    {
                                        unfinished = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            (unfinished, visited.len())
        }
        let depths = self.dom_dfs_depths(root);
        let bfs_order = self.bfs_order(root);
        let mut hint = None;
        while let (true, prev_hint) = tdmsc(self, &bfs_order, &depths, hint) {
            hint.replace(prev_hint);
        }
    }
}
