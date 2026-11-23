/-!
# Effects whose answer holds a borrow

An effect whose answer holds a borrow is an implicit borrowed argument written
in the row. `perform e()`
borrows from the source `e`. The `handle` that removes `e` reads `e` as the
loans of the value `v` in the arm's answer `k(v)`; the arm calls `k` there and
then, so `k` itself borrows what `v` borrows.

This file models only the loans, as lists of `(source, mode)`. It proves:

- reading `e` removes it, and leaves only the body's other loans and the loans
  of `v` (`read_sources`), so the result of a `handle` borrows nothing the
  check of its scope does not see (`handle_no_escape`);
- one call of `k` keeps every set of live loans free of conflicts when the
  body's loans and `v`'s loans are free of conflicts with each other
  (`once_ok`);
- several calls of `k` (resumption `ω`) whose results stay alive together are
  free of conflicts when `v` lends only shared loans (`many_ok_shared`), or
  when no kept result reads `e` (`many_ok_unread`);
- otherwise two kept results of a `ω` arm can hold the same mutable loan
  (`many_mut_conflict`), so the rule needs a condition before `ω` is allowed.
-/

namespace Proto.Nib.EffectLend

inductive Mode where
  | shr
  | mut
  deriving DecidableEq

structure Loan where
  src : Nat
  mode : Mode
  deriving DecidableEq

/-- Two loans conflict when they lend the same source and one is mutable. -/
def Conflict (a b : Loan) : Prop := a.src = b.src ∧ (a.mode = .mut ∨ b.mode = .mut)

/-- Live loans are fine when no two of them, at different positions, conflict. -/
def Ok (ls : List Loan) : Prop := ls.Pairwise (fun a b => ¬ Conflict a b)

def Sources (ls : List Loan) : List Nat := ls.map (·.src)

/-- Read the source `e` as the loans `lv` of the answer value: a loan of `e`
becomes `lv`, any other loan stays. -/
def read (e : Nat) (lv : List Loan) : List Loan → List Loan
  | [] => []
  | l :: ls => (if l.src = e then lv else [l]) ++ read e lv ls

theorem mem_read {e lv l} : ∀ {ls : List Loan},
    l ∈ read e lv ls → (l ∈ ls ∧ l.src ≠ e) ∨ l ∈ lv
  | [], h => by simp [read] at h
  | x :: xs, h => by
      simp only [read, List.mem_append] at h
      rcases h with h | h
      · by_cases hx : x.src = e
        · simp [hx] at h; exact .inr h
        · simp [hx] at h; subst h; exact .inl ⟨.head _, hx⟩
      · rcases mem_read h with ⟨h1, h2⟩ | h1
        · exact .inl ⟨.tail _ h1, h2⟩
        · exact .inr h1

/-- After the read, no loan of `e` is left unless `v` itself lends `e`. -/
theorem read_removes {e lv} (hv : ∀ l ∈ lv, l.src ≠ e) {ls : List Loan} :
    ∀ l ∈ read e lv ls, l.src ≠ e := by
  intro l hl
  rcases mem_read hl with ⟨_, h⟩ | h
  · exact h
  · exact hv l h

theorem read_sources {e lv ls} {s : Nat} (h : s ∈ Sources (read e lv ls)) :
    (s ∈ Sources ls ∧ s ≠ e) ∨ s ∈ Sources lv := by
  simp only [Sources, List.mem_map] at h ⊢
  obtain ⟨l, hl, rfl⟩ := h
  rcases mem_read hl with ⟨h1, h2⟩ | h1
  · exact .inl ⟨⟨l, h1, rfl⟩, h2⟩
  · exact .inr ⟨l, h1, rfl⟩

/-- The scope check: the body may borrow what the scope `Γ` holds and the
implicit source `e`; the answer `v` borrows only what the handler's scope
holds, which `Γ` includes. Then the `handle` borrows only from `Γ`, so a value
placed in a region that lives in `Γ` cannot leave the region's scope. -/
theorem handle_no_escape {Γ : List Nat} {e lv ls}
    (hb : ∀ s ∈ Sources ls, s ∈ Γ ∨ s = e) (hv : ∀ s ∈ Sources lv, s ∈ Γ) :
    ∀ s ∈ Sources (read e lv ls), s ∈ Γ := by
  intro s hs
  rcases read_sources hs with ⟨h1, h2⟩ | h1
  · rcases hb s h1 with h | h
    · exact h
    · exact absurd h h2
  · exact hv s h1

theorem conflict_symm {a b : Loan} (h : ¬ Conflict a b) : ¬ Conflict b a := by
  intro ⟨h1, h2⟩; exact h ⟨h1.symm, h2.symm⟩

/-- The loans the body keeps beside `e`. -/
def rest (e : Nat) (ls : List Loan) : List Loan := ls.filter (fun l => l.src ≠ e)

/-- How many loans of `e` the body holds. -/
def hits (e : Nat) (ls : List Loan) : Nat := (ls.filter (fun l => l.src = e)).length

/-- The read is the kept loans and one copy of `v`'s loans per loan of `e`. -/
theorem read_perm (e : Nat) (lv : List Loan) : ∀ ls : List Loan,
    (read e lv ls).Perm (rest e ls ++ (List.replicate (hits e ls) lv).flatten)
  | [] => by simp [read, rest, hits]
  | x :: xs => by
      have ih := read_perm e lv xs
      by_cases h : x.src = e
      · simp only [read, rest, hits, h, ite_true, List.filter_cons, decide_true,
          decide_not, Bool.not_true, Bool.false_eq_true, ite_false, List.length_cons,
          List.replicate_succ, List.flatten_cons]
        simp only [rest, hits, decide_not] at ih
        exact (ih.append_left lv).trans (List.perm_append_comm_assoc _ _ _)
      · simp only [read, rest, hits, h, ite_false, List.filter_cons, decide_false,
          decide_not, Bool.not_false, ite_true, Bool.false_eq_true, List.cons_append]
        simp only [rest, hits, decide_not] at ih
        exact ih.cons x

theorem ok_perm {xs ys : List Loan} (p : xs.Perm ys) : Ok xs ↔ Ok ys :=
  p.pairwise_iff (fun h => conflict_symm h)

theorem ok_append {xs ys : List Loan} :
    Ok (xs ++ ys) ↔ Ok xs ∧ Ok ys ∧ ∀ a ∈ xs, ∀ b ∈ ys, ¬ Conflict a b :=
  List.pairwise_append

theorem ok_sub {xs ys : List Loan} (h : xs.Sublist ys) : Ok ys → Ok xs := fun hy => hy.sublist h

theorem rest_sub (e : Nat) (ls : List Loan) : (rest e ls).Sublist ls := List.filter_sublist

/-- One call of `k`, as the implementation allows it: `perform e()` gives
one loan of `e`, so the result of the arm is free of conflicts when `v`'s loans
are, the body's other loans are, and the two sides do not conflict. -/
theorem once_ok {e lv ls} (h1 : hits e ls = 1) (hv : Ok lv) (hl : Ok (rest e ls))
    (hx : ∀ a ∈ rest e ls, ∀ b ∈ lv, ¬ Conflict a b) : Ok (read e lv ls) := by
  rw [ok_perm (read_perm e lv ls), h1]
  simpa using ok_append.2 ⟨hl, hv, hx⟩

/-- Every loan is shared. -/
def Shared (ls : List Loan) : Prop := ∀ l ∈ ls, l.mode = .shr

theorem shared_ok : ∀ {ls : List Loan}, Shared ls → Ok ls
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
      refine List.Pairwise.cons ?_ (shared_ok (fun l hl => h l (.tail _ hl)))
      intro b hb ⟨_, hm⟩
      have := h x (.head _); have := h b (.tail _ hb)
      rcases hm with hm | hm <;> simp_all

theorem mem_rep {b : Loan} {lv : List Loan} : ∀ {n : Nat}, b ∈ (List.replicate n lv).flatten → b ∈ lv
  | 0, h => by simp at h
  | n + 1, h => by
      simp only [List.replicate_succ, List.flatten_cons, List.mem_append] at h
      rcases h with h | h
      · exact h
      · exact mem_rep h

theorem mem_reps {b : Loan} {lv : List Loan} {e : Nat} : ∀ {lss : List (List Loan)},
    b ∈ (lss.map (fun ls => (List.replicate (hits e ls) lv).flatten)).flatten → b ∈ lv
  | [], h => by simp at h
  | _ :: _, h => by
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at h
      rcases h with h | h
      · exact mem_rep h
      · exact mem_reps h

theorem many_perm (e : Nat) (lv : List Loan) : ∀ lss : List (List Loan),
    ((lss.map (read e lv)).flatten).Perm
      ((lss.map (rest e)).flatten ++ (lss.map (fun ls => (List.replicate (hits e ls) lv).flatten)).flatten)
  | [] => by simp
  | ls :: lss => by
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      refine ((read_perm e lv ls).append (many_perm e lv lss)).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

/-- `ω`: the arm calls `k` once per body result `lss[i]` and keeps every
result alive together. When `v` lends only shared loans, the kept results
are free of conflicts as soon as the body's other loans are free of conflicts
with each other and with `v`'s loans. -/
theorem many_ok_shared {e lv} (hs : Shared lv) (lss : List (List Loan))
    (hl : Ok (lss.map (rest e)).flatten)
    (hx : ∀ a ∈ (lss.map (rest e)).flatten, ∀ b ∈ lv, ¬ Conflict a b) :
    Ok (lss.map (read e lv)).flatten := by
  rw [ok_perm (many_perm e lv lss)]
  refine ok_append.2 ⟨hl, shared_ok (fun l hl => hs l (mem_reps hl)), ?_⟩
  intro a ha b hb
  exact hx a ha b (mem_reps hb)

theorem read_unread {e lv} : ∀ {ls : List Loan}, hits e ls = 0 → read e lv ls = ls
  | [], _ => rfl
  | x :: xs, h => by
      by_cases hx : x.src = e
      · simp [hits, hx] at h
      · have : hits e xs = 0 := by simpa [hits, List.filter_cons, hx] using h
        simp [read, hx, read_unread this]

/-- `ω` where no kept result reads `e`: the read changes nothing. -/
theorem many_ok_unread {e lv} (lss : List (List Loan)) (hu : ∀ ls ∈ lss, hits e ls = 0)
    (hl : Ok lss.flatten) : Ok (lss.map (read e lv)).flatten := by
  have : lss.map (read e lv) = lss := by
    conv => rhs; rw [← List.map_id lss]
    exact List.map_congr_left (fun ls h => read_unread (hu ls h))
  rwa [this]

/-- Otherwise `ω` is unsound: `v` lends `a` mutably, and two kept results of
`k` each hold the loan of `e`, so both hold `a` mutably. -/
theorem many_mut_conflict :
    ¬ Ok ([[⟨1, .shr⟩], [⟨1, .shr⟩]].map (read 1 [⟨0, .mut⟩])).flatten := by
  simp [Ok, read, Conflict]

end Proto.Nib.EffectLend
