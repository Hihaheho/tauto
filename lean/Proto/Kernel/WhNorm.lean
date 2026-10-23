import Proto.Kernel.SNCand
import Proto.Kernel.Bidir

/-!
# Weak-head normal forms and conversion between them

The facts the completeness of the checker's `conv` rests on (no normalization yet):

* `Wh t` is the syntactic description of "no weak-head step": `Whnf t ↔ Wh t`;
* a reduct of a `Wh` term has the same head constructor and is again `Wh`;
* hence two convertible `Wh` terms have the same head and convertible components
  (`ConvW`): this is where confluence is used.
-/

namespace Proto.Kernel

open Tm

/-- The head constructor. -/
def hd : Tm → Nat
  | .var _ => 0
  | .sort _ => 1
  | .pi _ _ => 2
  | .lam _ => 3
  | .app _ _ => 4
  | .nat => 5
  | .zero => 6
  | .succ _ => 7
  | .natRec .. => 8

inductive Wh : Tm → Prop where
  | var (i : Nat) : Wh (var i)
  | sort (n : Nat) : Wh (sort n)
  | pi (A B : Tm) : Wh (pi A B)
  | lam (b : Tm) : Wh (lam b)
  | nat : Wh nat
  | zero : Wh zero
  | succ (n : Tm) : Wh (succ n)
  | app {f a : Tm} : Wh f → hd f ≠ 3 → Wh (app f a)
  | natRec {P z s n : Tm} : Wh n → hd n ≠ 6 → hd n ≠ 7 → Wh (natRec P z s n)

theorem hd_lam {t : Tm} (h : hd t = 3) : ∃ b, t = lam b := by
  cases t <;> simp [hd] at h; exact ⟨_, rfl⟩

theorem hd_zero {t : Tm} (h : hd t = 6) : t = zero := by
  cases t <;> simp [hd] at h; rfl

theorem hd_succ {t : Tm} (h : hd t = 7) : ∃ n, t = succ n := by
  cases t <;> simp [hd] at h; exact ⟨_, rfl⟩

theorem hd_app {t : Tm} (h : hd t = 4) : ∃ f a, t = app f a := by
  cases t <;> simp [hd] at h; exact ⟨_, _, rfl⟩

theorem hd_natRec {t : Tm} (h : hd t = 8) : ∃ P z s n, t = natRec P z s n := by
  cases t <;> simp [hd] at h; exact ⟨_, _, _, _, rfl⟩

theorem hd_pi {t : Tm} (h : hd t = 2) : ∃ A B, t = pi A B := by
  cases t <;> simp [hd] at h; exact ⟨_, _, rfl⟩

theorem hd_sort {t : Tm} (h : hd t = 1) : ∃ n, t = sort n := by
  cases t <;> simp [hd] at h; exact ⟨_, rfl⟩

theorem hd_var {t : Tm} (h : hd t = 0) : ∃ i, t = var i := by
  cases t <;> simp [hd] at h; exact ⟨_, rfl⟩

theorem hd_nat {t : Tm} (h : hd t = 5) : t = nat := by
  cases t <;> simp [hd] at h; rfl

/-! ## `Wh` is "no head step" -/

theorem Wh.whnf {t : Tm} (h : Wh t) : Whnf t := by
  induction h with
  | var => intro u r; cases r
  | sort => intro u r; cases r
  | pi => intro u r; cases r
  | lam => intro u r; cases r
  | nat => intro u r; cases r
  | zero => intro u r; cases r
  | succ => intro u r; cases r
  | app hf hl ih =>
      intro u r
      cases r with
      | beta => exact hl rfl
      | appL r' => exact ih _ r'
  | natRec hn h6 h7 ih =>
      intro u r
      cases r with
      | iotaZ => exact h6 rfl
      | iotaS => exact h7 rfl
      | recN r' => exact ih _ r'

theorem whnf_wh {t : Tm} : Whnf t → Wh t := by
  induction t with
  | var i => intro _; exact .var i
  | sort n => intro _; exact .sort n
  | pi A B => intro _; exact .pi A B
  | lam b => intro _; exact .lam b
  | nat => intro _; exact .nat
  | zero => intro _; exact .zero
  | succ n => intro _; exact .succ n
  | app f a ihf _ =>
      intro h
      refine .app (ihf (fun u r => h _ (.appL r))) ?_
      intro e
      obtain ⟨b, rfl⟩ := hd_lam e
      exact h _ (.beta b a)
  | natRec P z s n _ _ _ ihn =>
      intro h
      refine .natRec (ihn (fun u r => h _ (.recN r))) ?_ ?_
      · intro e; rw [hd_zero e] at h; exact h _ (.iotaZ P z s)
      · intro e; obtain ⟨m, rfl⟩ := hd_succ e; exact h _ (.iotaS P z s m)

theorem Wh.red1 {t u : Tm} (h : Wh t) (r : Red1 t u) : Wh u ∧ hd t = hd u := by
  induction h generalizing u with
  | var => cases r
  | sort => cases r
  | pi A B =>
      cases r with
      | piL r' => exact ⟨.pi _ _, rfl⟩
      | piR r' => exact ⟨.pi _ _, rfl⟩
  | lam b => cases r with | lam r' => exact ⟨.lam _, rfl⟩
  | nat => cases r
  | zero => cases r
  | succ n => cases r with | succ r' => exact ⟨.succ _, rfl⟩
  | @app f a hf hl ih =>
      cases r with
      | beta => exact (hl rfl).elim
      | appL r' =>
          obtain ⟨hf', e⟩ := ih r'
          exact ⟨.app hf' (by rw [← e]; exact hl), rfl⟩
      | appR r' => exact ⟨.app hf hl, rfl⟩
  | @natRec P z s n hn h6 h7 ih =>
      cases r with
      | iotaZ => exact (h6 rfl).elim
      | iotaS => exact (h7 rfl).elim
      | recP r' => exact ⟨.natRec hn h6 h7, rfl⟩
      | recZ r' => exact ⟨.natRec hn h6 h7, rfl⟩
      | recS r' => exact ⟨.natRec hn h6 h7, rfl⟩
      | recN r' =>
          obtain ⟨hn', e⟩ := ih r'
          exact ⟨.natRec hn' (by rw [← e]; exact h6) (by rw [← e]; exact h7), rfl⟩

theorem Wh.reds {t u : Tm} (h : Wh t) (r : Reds t u) : Wh u ∧ hd t = hd u := by
  induction r with
  | refl => exact ⟨h, rfl⟩
  | tail _ r ih =>
      obtain ⟨h1, e1⟩ := ih
      obtain ⟨h2, e2⟩ := h1.red1 r
      exact ⟨h2, e1.trans e2⟩

/-! ## Reduction of a `Wh` term -/

theorem Reds.var_inv {i : Nat} {t : Tm} (h : Reds (Tm.var i) t) : t = Tm.var i := by
  induction h with
  | refl => rfl
  | tail _ r ih => subst ih; cases r

theorem reds_app_wh {f a u : Tm} (h : Wh (app f a)) (r : Reds (app f a) u) :
    ∃ g b, u = app g b ∧ Reds f g ∧ Reds a b := by
  induction r with
  | refl => exact ⟨f, a, rfl, .refl _, .refl _⟩
  | tail r0 r ih =>
      obtain ⟨g, b, rfl, h1, h2⟩ := ih
      have hw : Wh (app g b) := (h.reds r0).1
      cases r with
      | beta =>
          cases hw with
          | app _ hl => exact (hl rfl).elim
      | appL r' => exact ⟨_, _, rfl, .tail h1 r', h2⟩
      | appR r' => exact ⟨_, _, rfl, h1, .tail h2 r'⟩

theorem reds_natRec_wh {P z s n u : Tm} (h : Wh (natRec P z s n)) (r : Reds (natRec P z s n) u) :
    ∃ P' z' s' n', u = natRec P' z' s' n' ∧ Reds P P' ∧ Reds z z' ∧ Reds s s' ∧ Reds n n' := by
  induction r with
  | refl => exact ⟨P, z, s, n, rfl, .refl _, .refl _, .refl _, .refl _⟩
  | tail r0 r ih =>
      obtain ⟨P', z', s', n', rfl, h1, h2, h3, h4⟩ := ih
      have hw : Wh (natRec P' z' s' n') := (h.reds r0).1
      cases r with
      | iotaZ =>
          cases hw with
          | natRec _ h6 _ => exact (h6 rfl).elim
      | iotaS =>
          cases hw with
          | natRec _ _ h7 => exact (h7 rfl).elim
      | recP r' => exact ⟨_, _, _, _, rfl, .tail h1 r', h2, h3, h4⟩
      | recZ r' => exact ⟨_, _, _, _, rfl, h1, .tail h2 r', h3, h4⟩
      | recS r' => exact ⟨_, _, _, _, rfl, h1, h2, .tail h3 r', h4⟩
      | recN r' => exact ⟨_, _, _, _, rfl, h1, h2, h3, .tail h4 r'⟩

/-! ## Convertible weak-head normal forms have convertible components -/

inductive ConvW : Tm → Tm → Prop where
  | var (i : Nat) : ConvW (var i) (var i)
  | sort (n : Nat) : ConvW (sort n) (sort n)
  | nat : ConvW nat nat
  | zero : ConvW zero zero
  | succ {n n'} : Conv n n' → ConvW (succ n) (succ n')
  | pi {A A' B B'} : Conv A A' → Conv B B' → ConvW (pi A B) (pi A' B')
  | lam {b b'} : Conv b b' → ConvW (lam b) (lam b')
  | app {f f' a a'} : Conv f f' → Conv a a' → ConvW (app f a) (app f' a')
  | natRec {P P' z z' s s' n n'} : Conv P P' → Conv z z' → Conv s s' → Conv n n' →
      ConvW (natRec P z s n) (natRec P' z' s' n')

theorem conv_wh {t u : Tm} (ht : Wh t) (hu : Wh u) (c : Conv t u) : ConvW t u := by
  obtain ⟨m, r1, r2⟩ := c
  cases ht with
  | var i =>
      have := r1.var_inv; subst this
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨j, rfl⟩ := hd_var (by rw [e]; rfl)
      cases r2.var_inv
      exact .var _
  | sort n =>
      have := r1.sort_inv; subst this
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨j, rfl⟩ := hd_sort (by rw [e]; rfl)
      cases r2.sort_inv
      exact .sort _
  | nat =>
      have := r1.nat_inv; subst this
      obtain ⟨_, e⟩ := hu.reds r2
      have := hd_nat (by rw [e]; rfl); subst this
      exact .nat
  | zero =>
      have := r1.zero_inv; subst this
      obtain ⟨_, e⟩ := hu.reds r2
      have := hd_zero (by rw [e]; rfl); subst this
      exact .zero
  | succ n =>
      obtain ⟨n1, rfl, h1⟩ := r1.succ_inv
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨n2, rfl⟩ := hd_succ (by rw [e]; rfl)
      obtain ⟨n3, e3, h3⟩ := r2.succ_inv
      cases e3
      exact .succ ⟨_, h1, h3⟩
  | pi A B =>
      obtain ⟨A1, B1, rfl, h1, h1'⟩ := r1.pi_inv
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨A2, B2, rfl⟩ := hd_pi (by rw [e]; rfl)
      obtain ⟨A3, B3, e3, h3, h3'⟩ := r2.pi_inv
      cases e3
      exact .pi ⟨_, h1, h3⟩ ⟨_, h1', h3'⟩
  | lam b =>
      obtain ⟨b1, rfl, h1⟩ := r1.lam_inv
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨b2, rfl⟩ := hd_lam (by rw [e]; rfl)
      obtain ⟨b3, e3, h3⟩ := r2.lam_inv
      cases e3
      exact .lam ⟨_, h1, h3⟩
  | @app f a hf hl =>
      obtain ⟨g, b, rfl, h1, h1'⟩ := reds_app_wh (.app hf hl) r1
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨f2, a2, rfl⟩ := hd_app (by rw [e]; rfl)
      obtain ⟨g2, b2, e3, h3, h3'⟩ := reds_app_wh hu r2
      cases e3
      exact .app ⟨_, h1, h3⟩ ⟨_, h1', h3'⟩
  | @natRec P z s n hn h6 h7 =>
      obtain ⟨P1, z1, s1, n1, rfl, h1, h2, h3, h4⟩ := reds_natRec_wh (.natRec hn h6 h7) r1
      obtain ⟨_, e⟩ := hu.reds r2
      obtain ⟨P2, z2, s2, n2, rfl⟩ := hd_natRec (by rw [e]; rfl)
      obtain ⟨P3, z3, s3, n3, e3, g1, g2, g3, g4⟩ := reds_natRec_wh hu r2
      cases e3
      exact .natRec ⟨_, h1, g1⟩ ⟨_, h2, g2⟩ ⟨_, h3, g3⟩ ⟨_, h4, g4⟩

/-! ## Existence of normal forms -/

def NormalT (t : Tm) : Prop := ∀ v, ¬ Red1 t v

theorem exists_nf {t : Tm} (h : SN t) : ∃ u, Reds t u ∧ ∀ v, ¬ Red1 u v := by
  induction h with
  | intro t _ ih =>
      by_cases hs : ∃ v, Red1 t v
      · obtain ⟨v, r⟩ := hs
        obtain ⟨u, hu, hn⟩ := ih v r
        exact ⟨u, Star.trans (Star.single r) hu, hn⟩
      · exact ⟨t, Star.refl _, fun v r => hs ⟨v, r⟩⟩

theorem exists_whnf {t : Tm} (h : SN t) : ∃ w, WhnfOf t w := by
  induction h with
  | intro t _ ih =>
      by_cases hs : ∃ v, HRed t v
      · obtain ⟨v, r⟩ := hs
        obtain ⟨w, hw⟩ := ih v r.red1
        exact ⟨w, Star.trans (Star.single r) hw.1, hw.2⟩
      · exact ⟨t, Star.refl _, fun v r => hs ⟨v, r⟩⟩

theorem normal_reds {n c : Tm} (hn : NormalT n) (r : Reds n c) : c = n := by
  rcases Reds.head r with rfl | ⟨u, r1, _⟩
  · rfl
  · exact (hn u r1).elim

/-- Normal forms are unique up to conversion. No normalization is assumed: this uses only
confluence (inside `Conv`) and that a normal term reduces only to itself. -/
theorem normal_unique {n m : Tm} (hn : NormalT n) (hm : NormalT m) (c : Conv n m) : n = m := by
  obtain ⟨d, h1, h2⟩ := c
  exact (normal_reds hn h1).symm.trans (normal_reds hm h2)

end Proto.Kernel
