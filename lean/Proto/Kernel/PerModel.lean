import Proto.Kernel.QuotEq
import Proto.Kernel.SNCand

/-!
# A model with partial equivalence relations

`G m L A A' S` says that the terms `A` and `A'` of `Proto/Kernel/Syntax.lean`
are equal types of level at most `m`, and that `S` relates the terms that are
equal elements of them. `S` is a partial equivalence relation on terms (`Good`):
the elements of a type are the terms `S` relates to themselves. As in `LRB`,
the relation is an index of an inductive graph, `L i` is the graph of the
universe `i < m` supplied from below, and every clause mentions a type only
through `Reds A _`.

* `nat`: two terms are equal numbers when they reduce to the same numeral.
* `sort i`: two terms are equal elements when they are equal types of the
  universe `i`; for `i = 0` their relation must also be proof irrelevant
  (`Irrel`: any two elements are equal).
* `Π`: functions are equal when they send equal arguments to equal results.
* `eqc X x y`, the reading of `Eq(X, x, y)`: any two terms are equal elements
  when `x` and `y` are equal in `X`, and there are none otherwise.
* `qc X r`, the reading of `Quot(X, r)`: elements of `X` are equal when a
  chain of steps, each an equality of `X` or a pair that `r` relates by an
  element of a proposition, joins them. This is the set of equivalence classes.

Two types that are related on both sides are what `G` needs over
`LRB`: the domain of a function type then determines its family up to
equality, so application does not have to compare the families of two
different substitutions.
-/

namespace Proto.Kernel

open Tm

abbrev Per := Tm → Tm → Prop

/-! ## Shapes that reduction keeps -/

def kind : Tm → Nat
  | .nat => 1
  | .sort _ => 2
  | .pi _ _ => 3
  | .app (.app (.app .zero _) _) _ => 4
  | .app (.app (.succ .zero) _) _ => 5
  | _ => 0

theorem Red1.eqc_inv {A x y u : Tm} (h : Red1 (eqc A x y) u) :
    ∃ A' x' y', u = eqc A' x' y' ∧ Reds A A' ∧ Reds x x' ∧ Reds y y' := by
  unfold eqc at h
  cases h with
  | appL h =>
      cases h with
      | appL h =>
          cases h with
          | appL h => cases h
          | appR h => exact ⟨_, _, _, rfl, Star.single h, Star.refl _, Star.refl _⟩
      | appR h => exact ⟨_, _, _, rfl, Star.refl _, Star.single h, Star.refl _⟩
  | appR h => exact ⟨_, _, _, rfl, Star.refl _, Star.refl _, Star.single h⟩

theorem Reds.eqc_inv {A x y u : Tm} (h : Reds (eqc A x y) u) :
    ∃ A' x' y', u = eqc A' x' y' ∧ Reds A A' ∧ Reds x x' ∧ Reds y y' := by
  induction h with
  | refl => exact ⟨_, _, _, rfl, Star.refl _, Star.refl _, Star.refl _⟩
  | tail _ r ih =>
      obtain ⟨A1, x1, y1, rfl, h1, h2, h3⟩ := ih
      obtain ⟨A2, x2, y2, rfl, h4, h5, h6⟩ := r.eqc_inv
      exact ⟨_, _, _, rfl, Star.trans h1 h4, Star.trans h2 h5, Star.trans h3 h6⟩

theorem Red1.qc_inv {A r u : Tm} (h : Red1 (qc A r) u) :
    ∃ A' r', u = qc A' r' ∧ Reds A A' ∧ Reds r r' := by
  unfold qc at h
  cases h with
  | appL h =>
      cases h with
      | appL h =>
          cases h with
          | succ h => cases h
      | appR h => exact ⟨_, _, rfl, Star.single h, Star.refl _⟩
  | appR h => exact ⟨_, _, rfl, Star.refl _, Star.single h⟩

theorem Reds.qc_inv {A r u : Tm} (h : Reds (qc A r) u) :
    ∃ A' r', u = qc A' r' ∧ Reds A A' ∧ Reds r r' := by
  induction h with
  | refl => exact ⟨_, _, rfl, Star.refl _, Star.refl _⟩
  | tail _ r ih =>
      obtain ⟨A1, r1, rfl, h1, h2⟩ := ih
      obtain ⟨A2, r2, rfl, h3, h4⟩ := r.qc_inv
      exact ⟨_, _, rfl, Star.trans h1 h3, Star.trans h2 h4⟩

/-- `A` reduces to a term all of whose reducts have kind `k`. -/
def KindAt (k : Nat) (A : Tm) : Prop := ∃ X, Reds A X ∧ ∀ u, Reds X u → kind u = k

namespace KindAt

theorem unique {k k' A} (h : KindAt k A) (h' : KindAt k' A) : k = k' := by
  obtain ⟨X, r, hX⟩ := h
  obtain ⟨Y, r', hY⟩ := h'
  obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
  rw [← hX M h1, ← hY M h2]

theorem nat {A} (r : Reds A .nat) : KindAt 1 A :=
  ⟨_, r, fun u h => by rw [h.nat_inv]; rfl⟩

theorem sort {A i} (r : Reds A (.sort i)) : KindAt 2 A :=
  ⟨_, r, fun u h => by rw [h.sort_inv]; rfl⟩

theorem pi {A A₁ B} (r : Reds A (.pi A₁ B)) : KindAt 3 A :=
  ⟨_, r, fun u h => by obtain ⟨_, _, rfl, _, _⟩ := h.pi_inv; rfl⟩

theorem eqc {A X x y} (r : Reds A (eqc X x y)) : KindAt 4 A :=
  ⟨_, r, fun u h => by obtain ⟨_, _, _, rfl, _⟩ := h.eqc_inv; rfl⟩

theorem qc {A X r'} (r : Reds A (qc X r')) : KindAt 5 A :=
  ⟨_, r, fun u h => by obtain ⟨_, _, rfl, _⟩ := h.qc_inv; rfl⟩

end KindAt

/-! ## Numerals -/

def num : Nat → Tm
  | 0 => .zero
  | k + 1 => .succ (num k)

theorem Reds.num_inv {k : Nat} {t : Tm} (h : Reds (num k) t) : t = num k := by
  induction k generalizing t with
  | zero => exact h.zero_inv
  | succ k ih =>
      obtain ⟨n', rfl, h'⟩ := Reds.succ_inv h
      rw [ih h']; rfl

/-- `a` and `b` reduce to the same numeral. -/
def NatR (a b : Tm) : Prop := ∃ k, Reds a (num k) ∧ Reds b (num k)

theorem Reds.num_unique {a : Tm} {k k' : Nat} (h : Reds a (num k)) (h' : Reds a (num k')) :
    num k = num k' := by
  obtain ⟨M, h1, h2⟩ := Reds.confluent h h'
  rw [← h1.num_inv, ← h2.num_inv]

/-! ## Partial equivalence relations -/

/-- A partial equivalence relation closed under conversion. -/
structure Good (S : Per) : Prop where
  symm : ∀ {a b}, S a b → S b a
  trans : ∀ {a b c}, S a b → S b c → S a c
  conv : ∀ {a a' b}, S a b → Conv a a' → S a' b

namespace Good
variable {S : Per}

theorem refl_l (h : Good S) {a b} (hab : S a b) : S a a := h.trans hab (h.symm hab)
theorem refl_r (h : Good S) {a b} (hab : S a b) : S b b := h.trans (h.symm hab) hab
theorem conv_r (h : Good S) {a b b'} (hab : S a b) (c : Conv b b') : S a b' :=
  h.symm (h.conv (h.symm hab) c)

end Good

theorem good_natR : Good NatR where
  symm := fun ⟨k, h1, h2⟩ => ⟨k, h2, h1⟩
  trans := fun ⟨k, h1, h2⟩ ⟨k', h3, h4⟩ => by
    have e := Reds.num_unique h2 h3
    exact ⟨k, h1, e ▸ h4⟩
  conv := fun ⟨k, h1, h2⟩ ⟨c, r1, r2⟩ => by
    obtain ⟨M, m1, m2⟩ := Reds.confluent h1 r1
    rw [m1.num_inv] at m2
    exact ⟨k, Star.trans r2 m2, h2⟩

theorem good_const (P : Prop) : Good (fun _ _ => P) where
  symm := id
  trans := fun h _ => h
  conv := fun h _ => h

/-- Proof irrelevance: any two elements are equal. -/
def Irrel (S : Per) : Prop := ∀ {a b c d}, S a b → S c d → S a d

/-- The equal elements of the universe `i`. -/
def USet (L : Nat → Tm → Tm → Per → Prop) (i : Nat) : Per :=
  fun T T' => ∃ S, L i T T' S ∧ (i = 0 → Irrel S)

/-- Equal functions send equal arguments to equal results. -/
def PiSet (SA : Per) (PB : Tm → Per) : Per :=
  fun f g => ∀ a b, SA a b → PB a (.app f a) (.app g b)

/-- `r a b` is a proposition with an element. -/
def QRel (L : Nat → Tm → Tm → Per → Prop) (r : Tm) : Per :=
  fun a b => ∃ T S, L 0 (.app (.app r a) b) T S ∧ ∃ p, S p p

/-- One step of a chain: an equality of the carrier, or a pair of its elements
that the relation relates. -/
def QBase (SX R : Per) : Per := fun a b => SX a b ∨ (SX a a ∧ SX b b ∧ R a b)

/-- The equivalence closure of a relation, without reflexivity. -/
inductive Chain (B : Per) : Tm → Tm → Prop where
  | fwd {a b} : B a b → Chain B a b
  | bwd {a b} : B b a → Chain B a b
  | trans {a b c} : Chain B a b → Chain B b c → Chain B a c

/-- The equal elements of the quotient of `SX` by `R`. -/
def QPer (SX R : Per) : Per := Chain (QBase SX R)

theorem Chain.symm {B : Per} {a b} (h : Chain B a b) : Chain B b a := by
  induction h with
  | fwd h => exact .bwd h
  | bwd h => exact .fwd h
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem QPer.field {SX R : Per} (hX : Good SX) {a b} (h : QPer SX R a b) : SX a a ∧ SX b b := by
  induction h with
  | fwd h =>
      rcases h with h | ⟨h1, h2, _⟩
      · exact ⟨hX.refl_l h, hX.refl_r h⟩
      · exact ⟨h1, h2⟩
  | bwd h =>
      rcases h with h | ⟨h1, h2, _⟩
      · exact ⟨hX.refl_r h, hX.refl_l h⟩
      · exact ⟨h2, h1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩

theorem QPer.of {SX R : Per} {a b} (h : SX a b) : QPer SX R a b := .fwd (.inl h)

theorem good_qper {SX R : Per} (hX : Good SX) : Good (QPer SX R) where
  symm := Chain.symm
  trans := Chain.trans
  conv := fun {a a' b} h c => by
    have ha := (QPer.field hX h).1
    exact .trans (QPer.of (hX.conv ha c)) h

theorem qper_congr {SX R R' : Per} (h : ∀ a b, SX a a → SX b b → (R a b ↔ R' a b)) :
    QPer SX R = QPer SX R' := by
  have side : ∀ {R R' : Per}, (∀ a b, SX a a → SX b b → (R a b → R' a b)) →
      ∀ a b, QPer SX R a b → QPer SX R' a b := by
    intro R R' hR a b hab
    induction hab with
    | fwd h =>
        rcases h with h | ⟨h1, h2, h3⟩
        · exact .fwd (.inl h)
        · exact .fwd (.inr ⟨h1, h2, hR _ _ h1 h2 h3⟩)
    | bwd h =>
        rcases h with h | ⟨h1, h2, h3⟩
        · exact .bwd (.inl h)
        · exact .bwd (.inr ⟨h1, h2, hR _ _ h1 h2 h3⟩)
    | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  funext a b
  exact propext ⟨side (fun a b h1 h2 => (h a b h1 h2).1) a b,
    side (fun a b h1 h2 => (h a b h1 h2).2) a b⟩

/-! ## The graph -/

inductive G (m : Nat) (L : Nat → Tm → Tm → Per → Prop) : Tm → Tm → Per → Prop where
  | nat {A A'} : Reds A .nat → Reds A' .nat → G m L A A' NatR
  | sort {A A' i} : i < m → Reds A (.sort i) → Reds A' (.sort i) → G m L A A' (USet L i)
  | pi {A A' A₁ A₁' B B' SA} {PB : Tm → Per} :
      Reds A (.pi A₁ B) → Reds A' (.pi A₁' B') → G m L A₁ A₁' SA →
      (∀ a a', SA a a' → G m L (inst B a) (inst B' a') (PB a)) →
      (∀ a a', SA a a' → PB a = PB a') →
      G m L A A' (PiSet SA PB)
  | eq {A A' X X' x x' y y' SX} :
      Reds A (eqc X x y) → Reds A' (eqc X' x' y') → G m L X X' SX → SX x x' → SX y y' →
      G m L A A' (fun _ _ => SX x y)
  | quot {A A' X X' r r' SX} : 0 < m →
      Reds A (qc X r) → Reds A' (qc X' r') → G m L X X' SX →
      (∀ a a' b b', SX a a' → SX b b' →
        ∃ S, L 0 (.app (.app r a) b) (.app (.app r' a') b') S) →
      G m L A A' (QPer SX (QRel L r))

/-- What `G m L` needs of the universes below `m`. -/
structure LOk (m : Nat) (L : Nat → Tm → Tm → Per → Prop) : Prop where
  good : ∀ i, i < m → ∀ {T T' S}, L i T T' S → Good S
  conv : ∀ i, i < m → ∀ {T T' S U}, L i T T' S → Conv T U → L i U T' S
  symm : ∀ i, i < m → ∀ {T T' S}, L i T T' S → L i T' T S
  trans : ∀ i, i < m → ∀ {T T' T'' S}, L i T T' S → L i T' T'' S → L i T T'' S
  uniq : ∀ i, i < m → ∀ {T T' T'' S S'}, L i T T' S → L i T T'' S' → S = S'

namespace G
variable {m : Nat} {L : Nat → Tm → Tm → Per → Prop}

theorem back {A A' U S} (h : G m L A A' S) (r : Reds U A) : G m L U A' S := by
  cases h with
  | nat r1 r2 => exact .nat (Star.trans r r1) r2
  | sort hi r1 r2 => exact .sort hi (Star.trans r r1) r2
  | pi r1 r2 hA hB hr => exact .pi (Star.trans r r1) r2 hA hB hr
  | eq r1 r2 hX hx hy => exact .eq (Star.trans r r1) r2 hX hx hy
  | quot hm r1 r2 hX hr => exact .quot hm (Star.trans r r1) r2 hX hr

theorem back_r {A A' U S} (h : G m L A A' S) (r : Reds U A') : G m L A U S := by
  cases h with
  | nat r1 r2 => exact .nat r1 (Star.trans r r2)
  | sort hi r1 r2 => exact .sort hi r1 (Star.trans r r2)
  | pi r1 r2 hA hB hr => exact .pi r1 (Star.trans r r2) hA hB hr
  | eq r1 r2 hX hx hy => exact .eq r1 (Star.trans r r2) hX hx hy
  | quot hm r1 r2 hX hr => exact .quot hm r1 (Star.trans r r2) hX hr

theorem good_uset (hL : LOk m L) {i} (hi : i < m) : Good (USet L i) where
  symm := fun ⟨S, h, ir⟩ => ⟨S, hL.symm i hi h, ir⟩
  trans := fun ⟨S, h1, ir⟩ ⟨S', h2, _⟩ => by
    have e := hL.uniq i hi (hL.symm i hi h1) h2
    subst e
    exact ⟨S, hL.trans i hi h1 h2, ir⟩
  conv := fun ⟨S, h, ir⟩ c => ⟨S, hL.conv i hi h c, ir⟩

theorem good (hL : LOk m L) {A A' S} (h : G m L A A' S) : Good S := by
  induction h with
  | nat => exact good_natR
  | sort hi => exact good_uset hL hi
  | eq => exact good_const _
  | quot _ _ _ _ _ ihX => exact good_qper ihX
  | @pi A A' A₁ A₁' B B' SA PB _ _ _ _ hr ihA ihB =>
      refine ⟨fun {f g} hfg a b hab => ?_, fun {f g k} h1 h2 a b hab => ?_,
        fun {f f' g} hfg c a b hab => ?_⟩
      · have hba := ihA.symm hab
        have := (ihB b a hba).symm (hfg b a hba)
        rwa [hr b a hba] at this
      · have haa := ihA.refl_l hab
        exact (ihB a a haa).trans (h1 a a haa) (h2 a b hab)
      · exact (ihB a b hab).conv (hfg a b hab) (Conv.app c (Conv.refl _))

theorem symm (hL : LOk m L) {A A' S} (h : G m L A A' S) : G m L A' A S := by
  induction h with
  | nat r1 r2 => exact .nat r2 r1
  | sort hi r1 r2 => exact .sort hi r2 r1
  | @pi A A' A₁ A₁' B B' SA PB r1 r2 hA hB hr ihA ihB =>
      have gA := hA.good hL
      refine .pi r2 r1 ihA (fun a' a h => ?_) (fun a a' h => hr a a' (gA.symm (gA.symm h)))
      have := ihB a a' (gA.symm h)
      rwa [hr a a' (gA.symm h)] at this
  | @eq A A' X X' x x' y y' SX r1 r2 hX hx hy ihX =>
      have gX := hX.good hL
      have e : (fun _ _ : Tm => SX x' y') = (fun _ _ => SX x y) := by
        funext _ _
        exact propext ⟨fun h => gX.trans hx (gX.trans h (gX.symm hy)),
          fun h => gX.trans (gX.symm hx) (gX.trans h hy)⟩
      rw [← e]
      exact .eq r2 r1 ihX (gX.symm hx) (gX.symm hy)
  | @quot A A' X X' r r' SX hm r1 r2 hX hr ihX =>
      have gX := hX.good hL
      have e : QPer SX (QRel L r') = QPer SX (QRel L r) := by
        apply qper_congr
        intro a b ha hb
        obtain ⟨S0, h0⟩ := hr a a b b ha hb
        constructor
        · rintro ⟨T, S, hS, p, hp⟩
          have := hL.uniq 0 hm hS (hL.symm 0 hm h0)
          subst this
          exact ⟨_, _, h0, p, hp⟩
        · rintro ⟨T, S, hS, p, hp⟩
          have := hL.uniq 0 hm hS h0
          subst this
          exact ⟨_, _, hL.symm 0 hm h0, p, hp⟩
      rw [← e]
      exact .quot hm r2 r1 ihX (fun a a' b b' ha hb =>
        let ⟨S, hS⟩ := hr a' a b' b (gX.symm ha) (gX.symm hb)
        ⟨S, hL.symm 0 hm hS⟩)

theorem fwd (hL : LOk m L) {A A' S} (h : G m L A A' S) : ∀ {U}, Reds A U → G m L U A' S := by
  induction h with
  | nat r1 r2 =>
      intro U r
      obtain ⟨M, h1, h2⟩ := Reds.confluent r1 r
      rw [h1.nat_inv] at h2
      exact .nat h2 r2
  | sort hi r1 r2 =>
      intro U r
      obtain ⟨M, h1, h2⟩ := Reds.confluent r1 r
      rw [h1.sort_inv] at h2
      exact .sort hi h2 r2
  | pi r1 r2 hA hB hr ihA ihB =>
      intro U r
      obtain ⟨M, h1, h2⟩ := Reds.confluent r1 r
      obtain ⟨A1, B1, rfl, e1, e2⟩ := h1.pi_inv
      exact .pi h2 r2 (ihA e1) (fun a a' h => ihB a a' h (Reds.inst e2 (Star.refl a))) hr
  | @eq A A' X X' x x' y y' SX r1 r2 hX hx hy ihX =>
      intro U r
      have gX := hX.good hL
      obtain ⟨M, h1, h2⟩ := Reds.confluent r1 r
      obtain ⟨X1, x1, y1, rfl, e1, e2, e3⟩ := h1.eqc_inv
      have e : (fun _ _ : Tm => SX x1 y1) = (fun _ _ => SX x y) := by
        funext _ _
        exact propext ⟨fun h => gX.conv_r (gX.conv h (Conv.of_reds' e2)) (Conv.of_reds' e3),
          fun h => gX.conv_r (gX.conv h (Conv.of_reds e2)) (Conv.of_reds e3)⟩
      rw [← e]
      exact .eq h2 r2 (ihX e1) (gX.conv hx (Conv.of_reds e2)) (gX.conv hy (Conv.of_reds e3))
  | @quot A A' X X' r r' SX hm r1 r2 hX hr ihX =>
      intro U rU
      obtain ⟨M, h1, h2⟩ := Reds.confluent r1 rU
      obtain ⟨X1, r3, rfl, e1, e2⟩ := h1.qc_inv
      have cr : ∀ a b, Conv (.app (.app r a) b) (.app (.app r3 a) b) := fun a b =>
        Conv.of_reds (Reds.app (Reds.app e2 (Star.refl _)) (Star.refl _))
      have e : QPer SX (QRel L r3) = QPer SX (QRel L r) := by
        apply qper_congr
        intro a b _ _
        constructor
        · rintro ⟨T, S, hS, hp⟩; exact ⟨T, S, hL.conv 0 hm hS (cr a b).symm, hp⟩
        · rintro ⟨T, S, hS, hp⟩; exact ⟨T, S, hL.conv 0 hm hS (cr a b), hp⟩
      rw [← e]
      exact .quot hm h2 r2 (ihX e1) (fun a a' b b' ha hb =>
        let ⟨S, hS⟩ := hr a a' b b' ha hb
        ⟨S, hL.conv 0 hm hS (cr a b)⟩)

theorem fwd_r (hL : LOk m L) {A A' S U} (h : G m L A A' S) (r : Reds A' U) : G m L A U S :=
  ((h.symm hL).fwd hL r).symm hL

theorem conv (hL : LOk m L) {A A' S U} (h : G m L A A' S) (c : Conv A U) : G m L U A' S := by
  obtain ⟨M, h1, h2⟩ := c
  exact (h.fwd hL h1).back h2

theorem conv_r (hL : LOk m L) {A A' S U} (h : G m L A A' S) (c : Conv A' U) : G m L A U S := by
  obtain ⟨M, h1, h2⟩ := c
  exact (h.fwd_r hL h1).back_r h2

/-- The left kind of a derivation. -/
theorem kindAt {A A' S} (h : G m L A A' S) :
    KindAt 1 A ∨ KindAt 2 A ∨ KindAt 3 A ∨ KindAt 4 A ∨ KindAt 5 A := by
  cases h with
  | nat r _ => exact .inl (.nat r)
  | sort _ r _ => exact .inr (.inl (.sort r))
  | pi r _ _ _ _ => exact .inr (.inr (.inl (.pi r)))
  | eq r _ _ _ _ => exact .inr (.inr (.inr (.inl (.eqc r))))
  | quot _ r _ _ _ => exact .inr (.inr (.inr (.inr (.qc r))))

theorem uniq (hL : LOk m L) {A A' S₁} (h₁ : G m L A A' S₁) :
    ∀ {A'' S₂}, G m L A A'' S₂ → S₁ = S₂ := by
  induction h₁ with
  | nat r =>
      intro A'' S₂ h₂
      cases h₂ with
      | nat => rfl
      | sort _ r' => cases (KindAt.nat r).unique (.sort r')
      | pi r' => cases (KindAt.nat r).unique (.pi r')
      | eq r' => cases (KindAt.nat r).unique (.eqc r')
      | quot _ r' => cases (KindAt.nat r).unique (.qc r')
  | sort hi r =>
      intro A'' S₂ h₂
      cases h₂ with
      | nat r' => cases (KindAt.sort r).unique (.nat r')
      | sort _ r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have e1 := h1.sort_inv
          have e2 := h2.sort_inv
          rw [e1] at e2
          cases e2
          rfl
      | pi r' => cases (KindAt.sort r).unique (.pi r')
      | eq r' => cases (KindAt.sort r).unique (.eqc r')
      | quot _ r' => cases (KindAt.sort r).unique (.qc r')
  | @pi A A' A₁ A₁' B B' SA PB r _ hA hB hr ihA ihB =>
      intro A'' S₂ h₂
      cases h₂ with
      | nat r' => cases (KindAt.pi r).unique (.nat r')
      | sort _ r' => cases (KindAt.pi r).unique (.sort r')
      | @pi _ _ C C' D D' SA2 PB2 r' _ hA2 hB2 _ =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨M1, N1, rfl, e1, e2⟩ := h1.pi_inv
          obtain ⟨M2, N2, e, f1, f2⟩ := h2.pi_inv
          cases e
          have eA : SA = SA2 := ihA ((hA2.fwd hL f1).back e1)
          subst eA
          have eB : ∀ a, SA a a → PB a = PB2 a := fun a ha =>
            ihB a a ha (((hB2 a a ha).fwd hL (Reds.inst f2 (Star.refl a))).back
              (Reds.inst e2 (Star.refl a)))
          have gA := hA.good hL
          funext f g
          apply propext
          constructor
          · intro H a b hab; rw [← eB a (gA.refl_l hab)]; exact H a b hab
          · intro H a b hab; rw [eB a (gA.refl_l hab)]; exact H a b hab
      | eq r' => cases (KindAt.pi r).unique (.eqc r')
      | quot _ r' => cases (KindAt.pi r).unique (.qc r')
  | @eq A A' X X' x x' y y' SX r _ hX _ _ ihX =>
      intro A'' S₂ h₂
      cases h₂ with
      | nat r' => cases (KindAt.eqc r).unique (.nat r')
      | sort _ r' => cases (KindAt.eqc r).unique (.sort r')
      | pi r' => cases (KindAt.eqc r).unique (.pi r')
      | @eq _ _ Z Z' z z' w w' SZ r' _ hZ _ _ =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨M1, m1, n1, rfl, e1, e2, e3⟩ := h1.eqc_inv
          obtain ⟨M2, m2, n2, e, f1, f2, f3⟩ := h2.eqc_inv
          simp only [eqc, Tm.app.injEq] at e
          obtain ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩ := e
          have eX : SX = SZ := ihX ((hZ.fwd hL f1).back e1)
          subst eX
          have gX := hX.good hL
          funext _ _
          have cx : Conv x z := ⟨_, e2, f2⟩
          have cy : Conv y w := ⟨_, e3, f3⟩
          exact propext ⟨fun h => gX.conv_r (gX.conv h cx) cy,
            fun h => gX.conv_r (gX.conv h cx.symm) cy.symm⟩
      | quot _ r' => cases (KindAt.eqc r).unique (.qc r')
  | @quot A A' X X' r0 r0' SX hm r _ hX _ ihX =>
      intro A'' S₂ h₂
      cases h₂ with
      | nat r' => cases (KindAt.qc r).unique (.nat r')
      | sort _ r' => cases (KindAt.qc r).unique (.sort r')
      | pi r' => cases (KindAt.qc r).unique (.pi r')
      | eq r' => cases (KindAt.qc r).unique (.eqc r')
      | @quot _ _ Z Z' s s' SZ _ r' _ hZ _ =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨M1, m1, rfl, e1, e2⟩ := h1.qc_inv
          obtain ⟨M2, m2, e, f1, f2⟩ := h2.qc_inv
          simp only [qc, Tm.app.injEq] at e
          obtain ⟨⟨_, rfl⟩, rfl⟩ := e
          have eX : SX = SZ := ihX ((hZ.fwd hL f1).back e1)
          subst eX
          have cr : ∀ a b, Conv (.app (.app r0 a) b) (.app (.app s a) b) := fun a b =>
            ⟨_, Reds.app (Reds.app e2 (Star.refl _)) (Star.refl _),
              Reds.app (Reds.app f2 (Star.refl _)) (Star.refl _)⟩
          apply qper_congr
          intro a b _ _
          constructor
          · rintro ⟨T, S, hS, hp⟩; exact ⟨T, S, hL.conv 0 hm hS (cr a b), hp⟩
          · rintro ⟨T, S, hS, hp⟩; exact ⟨T, S, hL.conv 0 hm hS (cr a b).symm, hp⟩

theorem uniq_r (hL : LOk m L) {A A' A'' S₁ S₂} (h₁ : G m L A' A S₁) (h₂ : G m L A'' A S₂) :
    S₁ = S₂ :=
  (h₁.symm hL).uniq hL (h₂.symm hL)

theorem trans (hL : LOk m L) {A A' S} (h₁ : G m L A A' S) :
    ∀ {A'' S'}, G m L A' A'' S' → G m L A A'' S := by
  induction h₁ with
  | nat r1 r =>
      intro A'' S' h₂
      cases h₂ with
      | nat _ r2 => exact .nat r1 r2
      | sort _ r' => cases (KindAt.nat r).unique (.sort r')
      | pi r' => cases (KindAt.nat r).unique (.pi r')
      | eq r' => cases (KindAt.nat r).unique (.eqc r')
      | quot _ r' => cases (KindAt.nat r).unique (.qc r')
  | sort hi r1 r =>
      intro A'' S' h₂
      cases h₂ with
      | nat r' => cases (KindAt.sort r).unique (.nat r')
      | sort _ r' r2 =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have e1 := h1.sort_inv
          have e2 := h2.sort_inv
          rw [e1] at e2
          cases e2
          exact .sort hi r1 r2
      | pi r' => cases (KindAt.sort r).unique (.pi r')
      | eq r' => cases (KindAt.sort r).unique (.eqc r')
      | quot _ r' => cases (KindAt.sort r).unique (.qc r')
  | @pi A A' A₁ A₁' B B' SA PB r1 r hA hB hr ihA ihB =>
      intro A'' S' h₂
      cases h₂ with
      | nat r' => cases (KindAt.pi r).unique (.nat r')
      | sort _ r' => cases (KindAt.pi r).unique (.sort r')
      | @pi _ _ C C' D D' SA2 PB2 r' r2 hA2 hB2 _ =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨M1, N1, rfl, e1, e2⟩ := h1.pi_inv
          obtain ⟨M2, N2, e, f1, f2⟩ := h2.pi_inv
          cases e
          have hA2' : G m L A₁' C' SA2 := (hA2.fwd hL f1).back e1
          have eA : SA = SA2 := uniq hL (hA.symm hL) hA2'
          subst eA
          have gA := hA.good hL
          refine .pi r1 r2 (ihA hA2') (fun a a'' h => ?_) hr
          have haa := gA.refl_l h
          have hB2' : G m L (inst B' a) (inst D' a'') (PB2 a) :=
            ((hB2 a a'' h).fwd hL (Reds.inst f2 (Star.refl a))).back (Reds.inst e2 (Star.refl a))
          exact ihB a a haa hB2'
      | eq r' => cases (KindAt.pi r).unique (.eqc r')
      | quot _ r' => cases (KindAt.pi r).unique (.qc r')
  | @eq A A' X X' x x' y y' SX r1 r hX hx hy ihX =>
      intro A'' S' h₂
      cases h₂ with
      | nat r' => cases (KindAt.eqc r).unique (.nat r')
      | sort _ r' => cases (KindAt.eqc r).unique (.sort r')
      | pi r' => cases (KindAt.eqc r).unique (.pi r')
      | @eq _ _ Z Z' z z' w w' SZ r' r2 hZ hz hw =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨M1, m1, n1, rfl, e1, e2, e3⟩ := h1.eqc_inv
          obtain ⟨M2, m2, n2, e, f1, f2, f3⟩ := h2.eqc_inv
          simp only [eqc, Tm.app.injEq] at e
          obtain ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩ := e
          have hZ' : G m L X' Z' SZ := (hZ.fwd hL f1).back e1
          have eX : SX = SZ := uniq hL (hX.symm hL) hZ'
          subst eX
          have gX := hX.good hL
          exact .eq r1 r2 (ihX hZ') (gX.trans hx (gX.conv hz ⟨_, f2, e2⟩))
            (gX.trans hy (gX.conv hw ⟨_, f3, e3⟩))
      | quot _ r' => cases (KindAt.eqc r).unique (.qc r')
  | @quot A A' X X' r0 r0' SX hm r1 r hX hr ihX =>
      intro A'' S' h₂
      cases h₂ with
      | nat r' => cases (KindAt.qc r).unique (.nat r')
      | sort _ r' => cases (KindAt.qc r).unique (.sort r')
      | pi r' => cases (KindAt.qc r).unique (.pi r')
      | eq r' => cases (KindAt.qc r).unique (.eqc r')
      | @quot _ _ Z Z' s s' SZ _ r' r2 hZ hs =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨M1, m1, rfl, e1, e2⟩ := h1.qc_inv
          obtain ⟨M2, m2, e, f1, f2⟩ := h2.qc_inv
          simp only [qc, Tm.app.injEq] at e
          obtain ⟨⟨_, rfl⟩, rfl⟩ := e
          have hZ' : G m L X' Z' SZ := (hZ.fwd hL f1).back e1
          have eX : SX = SZ := uniq hL (hX.symm hL) hZ'
          subst eX
          have gX := hX.good hL
          have cr : ∀ a b, Conv (.app (.app s a) b) (.app (.app r0' a) b) := fun a b =>
            ⟨_, Reds.app (Reds.app f2 (Star.refl _)) (Star.refl _),
              Reds.app (Reds.app e2 (Star.refl _)) (Star.refl _)⟩
          refine .quot hm r1 r2 (ihX hZ') (fun a a'' b b'' ha hb => ?_)
          obtain ⟨S1, h1⟩ := hr a a b b (gX.refl_l ha) (gX.refl_l hb)
          obtain ⟨S2, h2⟩ := hs a a'' b b'' ha hb
          have h2' := hL.conv 0 hm h2 (cr a b)
          have e := hL.uniq 0 hm (hL.symm 0 hm h1) h2'
          subst e
          exact ⟨S1, hL.trans 0 hm h1 h2'⟩

theorem mono {m' : Nat} {L' : Nat → Tm → Tm → Per → Prop} (hm : m ≤ m')
    (hL : ∀ i, i < m → L' i = L i) {A A' S} (h : G m L A A' S) : G m' L' A A' S := by
  induction h with
  | nat r1 r2 => exact .nat r1 r2
  | @sort A A' i hi r1 r2 =>
      have := G.sort (m := m') (L := L') (Nat.lt_of_lt_of_le hi hm) r1 r2
      have e : USet L' i = USet L i := by unfold USet; rw [hL i hi]
      rwa [e] at this
  | pi r1 r2 _ _ hr ihA ihB => exact .pi r1 r2 ihA ihB hr
  | eq r1 r2 _ hx hy ihX => exact .eq r1 r2 ihX hx hy
  | @quot A A' X X' r r' SX h0 r1 r2 _ hr ihX =>
      have := G.quot (m := m') (L := L') (Nat.lt_of_lt_of_le h0 hm) r1 r2 ihX
        (fun a a' b b' ha hb => by rw [hL 0 h0]; exact hr a a' b b' ha hb)
      have e : QRel L' r = QRel L r := by unfold QRel; rw [hL 0 h0]
      rwa [e] at this

end G

end Proto.Kernel
