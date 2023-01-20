use std::cell::UnsafeCell;

use crate::{
    set::{AssocSet, MemberSet},
    DomTree,
};

pub trait DJGraph: DomTree {
    type EdgeSet: MemberSet<Self::Identifier>;
    type NodeIter<'a>: Iterator<Item = Self::Identifier>
    where
        Self: 'a;
    fn create_edge_set(&self) -> Self::EdgeSet;
    fn node_iter<'a>(&'a self) -> Self::NodeIter<'a>;
    fn d_edge_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::EdgeSet>;
    fn d_edge_iter<'a>(&'a self, id: Self::Identifier) -> <<Self as DJGraph>::EdgeSet as MemberSet<Self::Identifier>>::MemberIter<'a> {
        unsafe { (*self.d_edge_cell(id).get()).iter() }
    }
    fn j_edge_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::EdgeSet>;
    fn j_edge_iter<'a>(&'a self, id: Self::Identifier) -> <<Self as DJGraph>::EdgeSet as MemberSet<Self::Identifier>>::MemberIter<'a> {
        unsafe { (*self.j_edge_cell(id).get()).iter() }
    }

    fn dj_dom_frontiers(&self, depths: &Self::Set<usize>, id : Self::Identifier) -> Self::EdgeSet {
        let mut data = self.create_edge_set();
        fn dfs<T : DJGraph>(graph: &T, depths: &T::Set<usize>, node: T::Identifier, data: &mut T::EdgeSet, target: T::Identifier) {
            for i in graph.j_edge_iter(node).filter(|z| depths.get(*z) <= depths.get(target)) {
                data.insert(i)
            }
            for i in graph.d_edge_iter(node) {
                dfs(graph, depths, i, data, target);
            }
        }
        dfs(self, depths, id, &mut data, id);
        data
    }

    fn dom_dfs_depths(&self, root: Self::Identifier) -> Self::Set<usize> {
        fn dfs<T : DJGraph>(graph: &T, depths: &mut T::Set<usize>, node: T::Identifier, depth: usize) {
            depths.set(node, depth);
            for i in graph.d_edge_iter(node) {
                dfs(graph, depths, i, depth + 1);
            }
        }
        let mut depths = self.create_set();
        dfs(self, &mut depths, root, 0);
        depths
    }

    fn populate_d_edges(&mut self) {
        for i in self.node_iter() {
            self.dom(i)
                .iter()
                .filter(|x| **x != i)
                .for_each(|d| unsafe { (*self.d_edge_cell(*d).get()).insert(i) });
        }
    }
    fn populate_j_edges(&mut self) {
        for i in self.node_iter() {
            for j in self.outgoing_edges(i) {
                if self.dom(j).map(|x| x != i).unwrap_or(false) {
                    unsafe {
                        (*self.j_edge_cell(i).get()).insert(j);
                    }
                }
            }
        }
    }
}

pub trait IteratedDomFrontier: DJGraph {
    // TODO
}
