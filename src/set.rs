/// Association set. This trait provides a mapping relation between X and Y.
pub trait AssocSet<X, Y: Clone + Default> {
    /// Given target key, return the associated attribute.
    fn get(&self, target: X) -> Y;
    /// Update the associated attribute of a given key.
    fn set(&mut self, key: X, val: Y);
}

/// Membership set. This is used to maintain the dominance frontiers.
pub trait MemberSet<T> {
    type MemberIter<'a>: Iterator<Item = T>
    where
        Self: 'a;
    /// Check if the set contains a target.
    fn contains(&self, target: T) -> bool;

    /// Iterate all members
    fn iter<'a>(&'a self) -> Self::MemberIter<'a>;

    /// Insert a new element to the set. The data structure is expected to maintain the
    /// uniqueness of its member on itself.
    fn insert(&mut self, target: T);
}

/// Similar to [`MemberSet`] but also provides merge operations
pub trait MergeSet<T>: MemberSet<T> {
    /// Check subset relation.
    fn subset(&self, other: &Self) -> bool;
    /// Collect all elements from the other set into current set.
    fn union(&mut self, other: &Self);
}
