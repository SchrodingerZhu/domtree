use crate::set::AssocSet;

/// Interfaces to run DFS on a graph.
pub trait DFSGraph {
    /// [`Self::Identifier`] is used to get/access nodes in user-defined graph data structure.
    /// For example, if the graph nodes are stored in a [`std::vec::Vec`], [`core::primitive::usize`] (the vector index)
    /// can be a good candidate.
    type Identifier: Clone + PartialEq + Eq + Copy;
    /// [`Self::Set`] is used to store some temporary data associated with the nodes. For example,
    /// in the case of using vector index mentioned above, [`std::vec::Vec`] itself can be a good choice for
    /// this association set. See [`AssocSet`] for requirements of the data structure.
    type Set<Y>: AssocSet<Self::Identifier, Y>
    where
        Y: Clone + Default;
    /// [`Self::SuccessorIter`] iterates over the outgoing edges of a single node. It is used in
    /// [`Self::outgoing_edges`].
    type SuccessorIter<'a>: Iterator<Item = Self::Identifier>
    where
        Self: 'a;

    /// Create a default initialized [`Self::Set`]
    fn create_set<Y>(&self) -> Self::Set<Y>
    where
        Y: Clone + Default;

    /// Get an iterator over the outgoing_edges of the given node.
    fn outgoing_edges<'a>(&'a self, id: Self::Identifier) -> Self::SuccessorIter<'a>;

    /// This method is automatically derived. It gives the post order sequence of the graph.
    fn post_order_sequence(&self, root: Self::Identifier) -> Vec<Self::Identifier> {
        let mut stack = Vec::new();
        let mut visited = self.create_set();
        let mut visitor = |i| stack.push(i);
        self.post_order_visit(&mut visited, root, &mut visitor);
        return stack;
    }

    /// This method is automatically derived. It visits the graph in post order.
    fn post_order_visit<F>(&self, set: &mut Self::Set<bool>, current: Self::Identifier, f: &mut F)
    where
        F: FnMut(Self::Identifier),
    {
        if set.get(current) {
            return;
        }

        set.set(current, true);

        for i in self.outgoing_edges(current) {
            self.post_order_visit(set, i, f);
        }

        f(current);
    }
}
