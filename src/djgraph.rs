use std::cell::UnsafeCell;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashSet, VecDeque};
use std::hash::Hash;

use crate::set::MergeSet;
use crate::{
    set::{AssocSet, MemberSet},
    DomTree,
};

/// [`DJGraph`] contains two kinds of edges:
/// - D-edges: edges from immediate dominator to its children (this forms the dominator tree)
/// - J-edges: edges in origin graph that does not overlap with any D-edge.
/// This trait provides facilities to calculate D-edges and J-edges. Based on [`DJGraph`],
/// one can also calculate the iterated dominance frontiers of a given set of nodes.
pub trait DJGraph: DomTree {
    /// A [`MemberSet`] used to maintain node identifiers.
    type NodeSet: MemberSet<Self::Identifier>;
    /// Iterator over all nodes of the graph.
    type NodeIter<'a>: Iterator<Item = Self::Identifier>
    where
        Self: 'a;
    /// Create an empty [`Self::NodeSet`].
    fn create_node_set(&self) -> Self::NodeSet;
    /// Get an iterator over all nodes of the graph.
    fn node_iter<'a>(&'a self) -> Self::NodeIter<'a>;
    /// Returns a reference to the D-edge storage.
    fn d_edge_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::NodeSet>;
    /// A helper function to get an iterator over D-edges of a given node.
    fn d_edge_iter<'a>(
        &'a self,
        id: Self::Identifier,
    ) -> <<Self as DJGraph>::NodeSet as MemberSet<Self::Identifier>>::MemberIter<'a> {
        unsafe { (*self.d_edge_cell(id).get()).iter() }
    }
    /// Returns a reference to the J-edge storage.
    fn j_edge_cell(&self, id: Self::Identifier) -> &UnsafeCell<Self::NodeSet>;
    /// A helper function to get an iterator over J-edges of a given node.
    fn j_edge_iter<'a>(
        &'a self,
        id: Self::Identifier,
    ) -> <<Self as DJGraph>::NodeSet as MemberSet<Self::Identifier>>::MemberIter<'a> {
        unsafe { (*self.j_edge_cell(id).get()).iter() }
    }

    /// Calculate the dominance frontiers of a given node using tree-walking algorithm
    /// on [`DJGraph`]. Better call [`Self::populate_d_edges`] and [`Self::populate_j_edges`]
    /// before using this function.
    /// For each node, this function gives the same result as it is calculated in
    /// [`crate::frontier::DominanceFrontier::populate_frontiers`], but the former method calculate
    /// it for single node, while the latter method will populate the DFs for the whole graph.
    /// The depths of nodes can be obtains by calling [`Self::dom_dfs_depths`].
    fn dj_dom_frontiers(&self, depths: &Self::Set<usize>, id: Self::Identifier) -> Self::NodeSet {
        let mut data = self.create_node_set();
        fn dfs<T: DJGraph>(
            graph: &T,
            depths: &T::Set<usize>,
            node: T::Identifier,
            data: &mut T::NodeSet,
            target: T::Identifier,
        ) {
            for i in graph
                .j_edge_iter(node)
                .filter(|z| depths.get(*z) <= depths.get(target))
            {
                data.insert(i)
            }
            for i in graph.d_edge_iter(node) {
                dfs(graph, depths, i, data, target);
            }
        }
        dfs(self, depths, id, &mut data, id);
        data
    }

    /// Calculate the iterated dominance frontiers (IDF) of given nodes.
    /// Better call [`Self::populate_d_edges`] and [`Self::populate_j_edges`]
    /// before using this function.
    /// DF+ is the fixed point of the transitive closure defined as the following:
    /// ```plaintext
    /// IDF[0](S) = DF(S)
    /// IDF[n + 1](S) = DF(S union IDF[n](S))
    /// ```
    /// The depths of nodes can be obtains by calling [`Self::dom_dfs_depths`].
    fn iterated_frontiers(&self, depths: &Self::Set<usize>, set: &Self::NodeSet) -> Self::NodeSet {
        struct Item<T>(usize, T);

        impl<T> Eq for Item<T> {}
        impl<T> Ord for Item<T> {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }

        impl<T> PartialEq<Item<T>> for Item<T> {
            fn eq(&self, other: &Self) -> bool {
                self.0.eq(&other.0)
            }
        }
        impl<T> PartialOrd for Item<T> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.0.partial_cmp(&other.0)
            }
        }

        let mut visited = self.create_set();
        let mut df_closure = self.create_node_set();
        let mut priority_queue = BinaryHeap::new();
        for i in set.iter() {
            priority_queue.push(Item(depths.get(i), i));
        }
        fn visit<T: DJGraph>(
            graph: &T,
            df_closure: &mut T::NodeSet,
            visited: &mut T::Set<bool>,
            heap: &mut BinaryHeap<Item<T::Identifier>>,
            depths: &T::Set<usize>,
            set: &T::NodeSet,
            y: T::Identifier,
            current: T::Identifier,
        ) {
            for z in graph
                .j_edge_iter(y)
                .filter(|z| depths.get(*z) <= depths.get(current))
            {
                if !df_closure.contains(z) {
                    df_closure.insert(z);
                    if !set.contains(z) {
                        heap.push(Item(depths.get(z), z));
                    }
                }
            }
            for z in graph.d_edge_iter(y) {
                if !visited.get(z) {
                    visited.set(z, true);
                    visit(graph, df_closure, visited, heap, depths, set, z, current);
                }
            }
        }
        while let Some(x) = priority_queue.pop() {
            visited.set(x.1, true);
            visit(
                self,
                &mut df_closure,
                &mut visited,
                &mut priority_queue,
                &depths,
                set,
                x.1,
                x.1,
            );
        }
        df_closure
    }
    /// Calculate the depths of nodes in the dom tree.
    fn dom_dfs_depths(&self, root: Self::Identifier) -> Self::Set<usize> {
        fn dfs<T: DJGraph>(
            graph: &T,
            depths: &mut T::Set<usize>,
            node: T::Identifier,
            depth: usize,
        ) {
            depths.set(node, depth);
            for i in graph.d_edge_iter(node) {
                dfs(graph, depths, i, depth + 1);
            }
        }
        let mut depths = self.create_set();
        dfs(self, &mut depths, root, 0);
        depths
    }
    /// Materialize all the D-edges of the graph. [`DomTree::populate_dom`] needs to be called first.
    fn populate_d_edges(&mut self) {
        for i in self.node_iter() {
            self.dom(i)
                .iter()
                .filter(|x| **x != i)
                .for_each(|d| unsafe { (*self.d_edge_cell(*d).get()).insert(i) });
        }
    }
    /// Materialize all the J-edges of the graph. [`DomTree::populate_dom`] needs to be called first.
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
