import Proto.ListSet

/-!
# Tags as finite extensional sets

This is the *logical equality* of tags. It intentionally does not
reorder a tag across any type constructor. A canonical executable
representation (with sorting / de-duplication) is a later layer.

Its laws (order and repeats of names do not matter) are those of
`ListSet.lean`.
-/

namespace Proto

/-- Two tag collections are equal when they contain the same names. -/
abbrev TagEq (xs ys : List String) : Prop := ListSet.Equiv xs ys

end Proto
