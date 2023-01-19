/// Association set. This trait provides a mapping relation between X and Y.
pub trait AssocSet<X, Y: Clone + Default> {
    /// Given target key, return the associated attribute.
    fn get(&self, target: X) -> Y;
    /// Update the associated attribute of a given key.
    fn set(&mut self, key: X, val: Y);
}

/// Membership set. This is used to maintain the dominance frontiers.
pub trait MemberSet<T> {
    /// Check if the set contains a target.
    fn contains(&self, target: T) -> bool;
    /// Insert a new element to the set. The data structure is expected to maintain the
    /// uniqueness of its member on itself.
    fn insert(&mut self, target: T);
}