use std::cell::UnsafeCell;

use crate::{DomTree, set::{MemberSet, AssocSet}};

// Iterate dominance frontiers using DJ-graph approach.
pub struct DJDomFrontierIter;

pub trait DJGraph : DomTree {
    type EdgeSet : MemberSet<Self::Identifier>;
    type DepthSet : AssocSet<Self::Identifier, usize>;

    fn d_edge_cell(&self) -> &UnsafeCell<Self::EdgeSet>;
    fn j_edge_cell(&self) -> &UnsafeCell<Self::EdgeSet>;

    fn dfs_depths(&self) -> Self::DepthSet;

    fn populate_d_edges(&mut self);
    fn populate_j_edges(&mut self);
}


pub trait IteratedDomFrontier : DJGraph {
    // TODO 
}