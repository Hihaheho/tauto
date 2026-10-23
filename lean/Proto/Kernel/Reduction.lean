import Proto.Kernel.Syntax

/-!
# Reduction and conversion

`Red1` is one step of beta or iota (the iota rules are the ones the kernel
generates for `Nat_rec`), anywhere in a term. `Reds` is its reflexive
transitive closure and `Conv` the conversion the kernel decides.

Confluence is proved with parallel reduction and its complete development
(Takahashi). Conversion is then an equivalence, and the head constructors
`pi`/`sort`/`nat` are injective for it: the facts the typing rules need.
-/

namespace Proto.Kernel

open Tm

inductive Star (R : Tm → Tm → Prop) : Tm → Tm → Prop where
  | refl (a : Tm) : Star R a a
  | tail {a b c : Tm} : Star R a b → R b c → Star R a c

namespace Star
variable {R S : Tm → Tm → Prop}

theorem single {a b} (h : R a b) : Star R a b := .tail (.refl a) h

theorem trans {a b c} (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  induction h2 with
  | refl => exact h1
  | tail _ r ih => exact .tail ih r

theorem lift (f : Tm → Tm) (h : ∀ a b, R a b → S (f a) (f b)) {a b} (s : Star R a b) :
    Star S (f a) (f b) := by
  induction s with
  | refl => exact .refl _
  | tail _ r ih => exact .tail ih (h _ _ r)

theorem mono (h : ∀ a b, R a b → S a b) {a b} (s : Star R a b) : Star S a b := by
  induction s with
  | refl => exact .refl _
  | tail _ r ih => exact .tail ih (h _ _ r)

end Star

/-! ## One-step reduction -/

inductive Red1 : Tm → Tm → Prop where
  | beta (b a : Tm) : Red1 (app (lam b) a) (inst b a)
  | iotaZ (P z s : Tm) : Red1 (natRec P z s zero) z
  | iotaS (P z s n : Tm) : Red1 (natRec P z s (succ n)) (app (app s n) (natRec P z s n))
  | piL {A A' B} : Red1 A A' → Red1 (pi A B) (pi A' B)
  | piR {A B B'} : Red1 B B' → Red1 (pi A B) (pi A B')
  | lam {b b'} : Red1 b b' → Red1 (lam b) (lam b')
  | appL {f f' a} : Red1 f f' → Red1 (app f a) (app f' a)
  | appR {f a a'} : Red1 a a' → Red1 (app f a) (app f a')
  | succ {n n'} : Red1 n n' → Red1 (succ n) (succ n')
  | recP {P P' z s n} : Red1 P P' → Red1 (natRec P z s n) (natRec P' z s n)
  | recZ {P z z' s n} : Red1 z z' → Red1 (natRec P z s n) (natRec P z' s n)
  | recS {P z s s' n} : Red1 s s' → Red1 (natRec P z s n) (natRec P z s' n)
  | recN {P z s n n'} : Red1 n n' → Red1 (natRec P z s n) (natRec P z s n')

abbrev Reds := Star Red1

/-- Conversion: two terms reduce to a common term. -/
def Conv (a b : Tm) : Prop := ∃ c, Reds a c ∧ Reds b c

namespace Reds

theorem pi {A A' B B'} (hA : Reds A A') (hB : Reds B B') : Reds (pi A B) (pi A' B') :=
  Star.trans (Star.lift (fun x => Tm.pi x B) (fun _ _ => .piL) hA)
    (Star.lift (fun x => Tm.pi A' x) (fun _ _ => .piR) hB)

theorem lam {b b'} (h : Reds b b') : Reds (lam b) (lam b') :=
  Star.lift Tm.lam (fun _ _ => .lam) h

theorem app {f f' a a'} (hf : Reds f f') (ha : Reds a a') : Reds (app f a) (app f' a') :=
  Star.trans (Star.lift (fun x => Tm.app x a) (fun _ _ => .appL) hf)
    (Star.lift (fun x => Tm.app f' x) (fun _ _ => .appR) ha)

theorem succ {n n'} (h : Reds n n') : Reds (succ n) (succ n') :=
  Star.lift Tm.succ (fun _ _ => .succ) h

theorem natRec {P P' z z' s s' n n'} (hP : Reds P P') (hz : Reds z z') (hs : Reds s s')
    (hn : Reds n n') : Reds (natRec P z s n) (natRec P' z' s' n') :=
  Star.trans (Star.lift (fun x => Tm.natRec x z s n) (fun _ _ => .recP) hP)
    (Star.trans (Star.lift (fun x => Tm.natRec P' x s n) (fun _ _ => .recZ) hz)
      (Star.trans (Star.lift (fun x => Tm.natRec P' z' x n) (fun _ _ => .recS) hs)
        (Star.lift (fun x => Tm.natRec P' z' s' x) (fun _ _ => .recN) hn)))

end Reds

/-! ## Parallel reduction -/

inductive Par : Tm → Tm → Prop where
  | var (i : Nat) : Par (var i) (var i)
  | sort (n : Nat) : Par (sort n) (sort n)
  | pi {A A' B B'} : Par A A' → Par B B' → Par (pi A B) (pi A' B')
  | lam {b b'} : Par b b' → Par (lam b) (lam b')
  | app {f f' a a'} : Par f f' → Par a a' → Par (app f a) (app f' a')
  | beta {b b' a a'} : Par b b' → Par a a' → Par (app (lam b) a) (inst b' a')
  | nat : Par nat nat
  | zero : Par zero zero
  | succ {n n'} : Par n n' → Par (succ n) (succ n')
  | natRec {P P' z z' s s' n n'} :
      Par P P' → Par z z' → Par s s' → Par n n' → Par (natRec P z s n) (natRec P' z' s' n')
  | iotaZ {P P' z z' s s'} :
      Par P P' → Par z z' → Par s s' → Par (natRec P z s zero) z'
  | iotaS {P P' z z' s s' n n'} :
      Par P P' → Par z z' → Par s s' → Par n n' →
      Par (natRec P z s (succ n)) (app (app s' n') (natRec P' z' s' n'))

theorem Par.refl (t : Tm) : Par t t := by
  induction t with
  | var i => exact .var i
  | sort n => exact .sort n
  | pi A B ihA ihB => exact .pi ihA ihB
  | lam b ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | nat => exact .nat
  | zero => exact .zero
  | succ n ih => exact .succ ih
  | natRec P z s n ihP ihz ihs ihn => exact .natRec ihP ihz ihs ihn

theorem Par.ren {t t'} (h : Par t t') : ∀ ξ, Par (ren ξ t) (ren ξ t') := by
  induction h with
  | var i => intro ξ; exact .var _
  | sort n => intro ξ; exact .sort n
  | pi _ _ ihA ihB => intro ξ; exact .pi (ihA ξ) (ihB _)
  | lam _ ih => intro ξ; exact .lam (ih _)
  | app _ _ ihf iha => intro ξ; exact .app (ihf ξ) (iha ξ)
  | beta _ _ ihb iha =>
      intro ξ
      have := Par.beta (ihb (upR ξ)) (iha ξ)
      rwa [← ren_inst] at this
  | nat => intro ξ; exact .nat
  | zero => intro ξ; exact .zero
  | succ _ ih => intro ξ; exact .succ (ih ξ)
  | natRec _ _ _ _ ihP ihz ihs ihn => intro ξ; exact .natRec (ihP ξ) (ihz ξ) (ihs ξ) (ihn ξ)
  | iotaZ _ _ _ ihP ihz ihs => intro ξ; exact .iotaZ (ihP ξ) (ihz ξ) (ihs ξ)
  | iotaS _ _ _ _ ihP ihz ihs ihn =>
      intro ξ; exact .iotaS (ihP ξ) (ihz ξ) (ihs ξ) (ihn ξ)

theorem Par.up {σ τ : Nat → Tm} (h : ∀ i, Par (σ i) (τ i)) : ∀ i, Par (up σ i) (up τ i) := by
  intro i
  cases i with
  | zero => exact .var 0
  | succ n => exact (h n).ren Nat.succ

theorem Par.subst {t t'} (h : Par t t') :
    ∀ {σ τ : Nat → Tm}, (∀ i, Par (σ i) (τ i)) → Par (subst σ t) (subst τ t') := by
  induction h with
  | var i => intro σ τ hs; exact hs i
  | sort n => intro σ τ hs; exact .sort n
  | pi _ _ ihA ihB => intro σ τ hs; exact .pi (ihA hs) (ihB (Par.up hs))
  | lam _ ih => intro σ τ hs; exact .lam (ih (Par.up hs))
  | app _ _ ihf iha => intro σ τ hs; exact .app (ihf hs) (iha hs)
  | beta _ _ ihb iha =>
      intro σ τ hs
      have := Par.beta (ihb (Par.up hs)) (iha hs)
      rwa [← subst_inst] at this
  | nat => intro σ τ hs; exact .nat
  | zero => intro σ τ hs; exact .zero
  | succ _ ih => intro σ τ hs; exact .succ (ih hs)
  | natRec _ _ _ _ ihP ihz ihs ihn =>
      intro σ τ hs; exact .natRec (ihP hs) (ihz hs) (ihs hs) (ihn hs)
  | iotaZ _ _ _ ihP ihz ihs => intro σ τ hs; exact .iotaZ (ihP hs) (ihz hs) (ihs hs)
  | iotaS _ _ _ _ ihP ihz ihs ihn =>
      intro σ τ hs; exact .iotaS (ihP hs) (ihz hs) (ihs hs) (ihn hs)

theorem Par.inst {b b' a a'} (hb : Par b b') (ha : Par a a') : Par (inst b a) (inst b' a') := by
  refine hb.subst ?_
  intro i
  cases i with
  | zero => exact ha
  | succ n => exact .var n

theorem Red1.par {a b} (h : Red1 a b) : Par a b := by
  induction h with
  | beta b a => exact .beta (Par.refl _) (Par.refl _)
  | iotaZ P z s => exact .iotaZ (Par.refl _) (Par.refl _) (Par.refl _)
  | iotaS P z s n => exact .iotaS (Par.refl _) (Par.refl _) (Par.refl _) (Par.refl _)
  | piL _ ih => exact .pi ih (Par.refl _)
  | piR _ ih => exact .pi (Par.refl _) ih
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | succ _ ih => exact .succ ih
  | recP _ ih => exact .natRec ih (Par.refl _) (Par.refl _) (Par.refl _)
  | recZ _ ih => exact .natRec (Par.refl _) ih (Par.refl _) (Par.refl _)
  | recS _ ih => exact .natRec (Par.refl _) (Par.refl _) ih (Par.refl _)
  | recN _ ih => exact .natRec (Par.refl _) (Par.refl _) (Par.refl _) ih

theorem Par.reds {a b} (h : Par a b) : Reds a b := by
  induction h with
  | var i => exact .refl _
  | sort n => exact .refl _
  | pi _ _ ihA ihB => exact Reds.pi ihA ihB
  | lam _ ih => exact Reds.lam ih
  | app _ _ ihf iha => exact Reds.app ihf iha
  | beta hb ha ihb iha =>
      exact Star.trans (Reds.app (Reds.lam ihb) iha) (Star.single (.beta _ _))
  | nat => exact .refl _
  | zero => exact .refl _
  | succ _ ih => exact Reds.succ ih
  | natRec _ _ _ _ ihP ihz ihs ihn => exact Reds.natRec ihP ihz ihs ihn
  | iotaZ _ _ _ ihP ihz ihs =>
      exact Star.trans (Star.single (.iotaZ _ _ _)) ihz
  | iotaS _ _ _ _ ihP ihz ihs ihn =>
      exact Star.trans (Star.single (.iotaS _ _ _ _))
        (Reds.app (Reds.app ihs ihn) (Reds.natRec ihP ihz ihs ihn))

/-! ## Complete development and confluence -/

def develop : Tm → Tm
  | var i => var i
  | sort n => sort n
  | pi A B => pi (develop A) (develop B)
  | lam b => lam (develop b)
  | app (lam b) a => inst (develop b) (develop a)
  | app f a => app (develop f) (develop a)
  | nat => nat
  | zero => zero
  | succ n => succ (develop n)
  | natRec P z s zero => develop z
  | natRec P z s (succ n) => app (app (develop s) (develop n)) (natRec (develop P) (develop z) (develop s) (develop n))
  | natRec P z s n => natRec (develop P) (develop z) (develop s) (develop n)

theorem Par.dev {t t'} (h : Par t t') : Par t' (develop t) := by
  induction h with
  | var i => exact .var i
  | sort n => exact .sort n
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ ih => exact .lam ih
  | app hf ha ihf iha =>
      rename_i f f' a a'
      cases f with
      | lam b =>
          cases hf with
          | lam hb =>
              rename_i b'
              cases ihf with
              | lam ihb => exact .beta ihb iha
      | var _ => exact .app ihf iha
      | sort _ => exact .app ihf iha
      | pi _ _ => exact .app ihf iha
      | app _ _ => exact .app ihf iha
      | nat => exact .app ihf iha
      | zero => exact .app ihf iha
      | succ _ => exact .app ihf iha
      | natRec _ _ _ _ => exact .app ihf iha
  | beta _ _ ihb iha => exact Par.inst ihb iha
  | nat => exact .nat
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | natRec hP hz hs hn ihP ihz ihs ihn =>
      rename_i P P' z z' s s' n n'
      cases n with
      | zero =>
          cases hn
          exact .iotaZ ihP ihz ihs
      | succ m =>
          cases hn with
          | succ hm =>
              cases ihn with
              | succ ihm => exact .iotaS ihP ihz ihs ihm
      | var _ => exact .natRec ihP ihz ihs ihn
      | sort _ => exact .natRec ihP ihz ihs ihn
      | pi _ _ => exact .natRec ihP ihz ihs ihn
      | lam _ => exact .natRec ihP ihz ihs ihn
      | app _ _ => exact .natRec ihP ihz ihs ihn
      | nat => exact .natRec ihP ihz ihs ihn
      | natRec _ _ _ _ => exact .natRec ihP ihz ihs ihn
  | iotaZ _ _ _ ihP ihz ihs => exact ihz
  | iotaS _ _ _ _ ihP ihz ihs ihn =>
      exact .app (.app ihs ihn) (.natRec ihP ihz ihs ihn)

theorem Par.diamond {t a b} (h1 : Par t a) (h2 : Par t b) : ∃ c, Par a c ∧ Par b c :=
  ⟨develop t, h1.dev, h2.dev⟩

theorem Par.strip {t a b} (h1 : Par t a) (h2 : Star Par t b) : ∃ c, Star Par a c ∧ Par b c := by
  induction h2 generalizing a with
  | refl => exact ⟨a, .refl _, h1⟩
  | tail _ r ih =>
      obtain ⟨c, hc1, hc2⟩ := ih h1
      obtain ⟨d, hd1, hd2⟩ := Par.diamond hc2 r
      exact ⟨d, .tail hc1 hd1, hd2⟩

theorem Par.confluent {t a b} (h1 : Star Par t a) (h2 : Star Par t b) :
    ∃ c, Star Par a c ∧ Star Par b c := by
  induction h1 generalizing b with
  | refl => exact ⟨b, h2, .refl _⟩
  | tail _ r ih =>
      obtain ⟨c, hc1, hc2⟩ := ih h2
      obtain ⟨d, hd1, hd2⟩ := Par.strip r hc1
      exact ⟨d, hd1, .tail hc2 hd2⟩

theorem reds_par {a b} (h : Reds a b) : Star Par a b := Star.mono (fun _ _ r => r.par) h
theorem par_reds {a b} (h : Star Par a b) : Reds a b := by
  induction h with
  | refl => exact .refl _
  | tail _ r ih => exact Star.trans ih r.reds

theorem Reds.confluent {t a b} (h1 : Reds t a) (h2 : Reds t b) : ∃ c, Reds a c ∧ Reds b c := by
  obtain ⟨c, hc1, hc2⟩ := Par.confluent (reds_par h1) (reds_par h2)
  exact ⟨c, par_reds hc1, par_reds hc2⟩

/-! ## Conversion -/

namespace Conv

theorem refl (a : Tm) : Conv a a := ⟨a, .refl _, .refl _⟩

theorem symm {a b} (h : Conv a b) : Conv b a := by
  obtain ⟨c, h1, h2⟩ := h; exact ⟨c, h2, h1⟩

theorem trans {a b c} (h1 : Conv a b) (h2 : Conv b c) : Conv a c := by
  obtain ⟨d, ha, hb⟩ := h1
  obtain ⟨e, hb', hc⟩ := h2
  obtain ⟨f, hd, he⟩ := Reds.confluent hb hb'
  exact ⟨f, Star.trans ha hd, Star.trans hc he⟩

theorem of_reds {a b} (h : Reds a b) : Conv a b := ⟨b, h, .refl _⟩
theorem of_reds' {a b} (h : Reds b a) : Conv a b := ⟨a, .refl _, h⟩
theorem of_red1 {a b} (h : Red1 a b) : Conv a b := of_reds (Star.single h)

theorem pi {A A' B B'} (h1 : Conv A A') (h2 : Conv B B') : Conv (pi A B) (pi A' B') := by
  obtain ⟨c, a1, a2⟩ := h1
  obtain ⟨d, b1, b2⟩ := h2
  exact ⟨Tm.pi c d, Reds.pi a1 b1, Reds.pi a2 b2⟩

theorem lam {b b'} (h : Conv b b') : Conv (lam b) (lam b') := by
  obtain ⟨c, a1, a2⟩ := h
  exact ⟨Tm.lam c, Reds.lam a1, Reds.lam a2⟩

theorem app {f f' a a'} (h1 : Conv f f') (h2 : Conv a a') : Conv (app f a) (app f' a') := by
  obtain ⟨c, a1, a2⟩ := h1
  obtain ⟨d, b1, b2⟩ := h2
  exact ⟨Tm.app c d, Reds.app a1 b1, Reds.app a2 b2⟩

theorem succ {n n'} (h : Conv n n') : Conv (succ n) (succ n') := by
  obtain ⟨c, a1, a2⟩ := h
  exact ⟨Tm.succ c, Reds.succ a1, Reds.succ a2⟩

end Conv

/-! ## Reduction commutes with renaming and substitution -/

theorem Red1.ren {a b} (h : Red1 a b) : ∀ ξ, Red1 (ren ξ a) (ren ξ b) := by
  induction h with
  | beta b a =>
      intro ξ
      have := Red1.beta (Proto.Kernel.ren (upR ξ) b) (Proto.Kernel.ren ξ a)
      rw [← ren_inst] at this
      exact this
  | iotaZ P z s => intro ξ; exact .iotaZ _ _ _
  | iotaS P z s n => intro ξ; exact .iotaS _ _ _ _
  | piL _ ih => intro ξ; exact .piL (ih ξ)
  | piR _ ih => intro ξ; exact .piR (ih _)
  | lam _ ih => intro ξ; exact .lam (ih _)
  | appL _ ih => intro ξ; exact .appL (ih ξ)
  | appR _ ih => intro ξ; exact .appR (ih ξ)
  | succ _ ih => intro ξ; exact .succ (ih ξ)
  | recP _ ih => intro ξ; exact .recP (ih ξ)
  | recZ _ ih => intro ξ; exact .recZ (ih ξ)
  | recS _ ih => intro ξ; exact .recS (ih ξ)
  | recN _ ih => intro ξ; exact .recN (ih ξ)

theorem Reds.ren {a b} (h : Reds a b) (ξ : Nat → Nat) : Reds (Proto.Kernel.ren ξ a) (Proto.Kernel.ren ξ b) :=
  Star.lift (Proto.Kernel.ren ξ) (fun _ _ r => r.ren ξ) h

theorem Conv.ren {a b} (h : Conv a b) (ξ : Nat → Nat) : Conv (Proto.Kernel.ren ξ a) (Proto.Kernel.ren ξ b) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨Proto.Kernel.ren ξ c, h1.ren ξ, h2.ren ξ⟩

theorem Reds.inst {b b' a a'} (hb : Reds b b') (ha : Reds a a') :
    Reds (Proto.Kernel.inst b a) (Proto.Kernel.inst b' a') :=
  par_reds (Star.trans
    (Star.lift (fun x => Proto.Kernel.inst x a) (fun _ _ r => Par.inst r (Par.refl a)) (reds_par hb))
    (Star.lift (fun x => Proto.Kernel.inst b' x) (fun _ _ r => Par.inst (Par.refl b') r) (reds_par ha)))

theorem Conv.inst {b b' a a'} (hb : Conv b b') (ha : Conv a a') :
    Conv (Proto.Kernel.inst b a) (Proto.Kernel.inst b' a') := by
  obtain ⟨c, h1, h2⟩ := hb
  obtain ⟨d, k1, k2⟩ := ha
  exact ⟨Proto.Kernel.inst c d, Reds.inst h1 k1, Reds.inst h2 k2⟩


theorem Red1.subst {a b} (h : Red1 a b) : ∀ σ, Red1 (Proto.Kernel.subst σ a) (Proto.Kernel.subst σ b) := by
  induction h with
  | beta b a =>
      intro σ
      have := Red1.beta (Proto.Kernel.subst (up σ) b) (Proto.Kernel.subst σ a)
      rw [← subst_inst] at this
      exact this
  | iotaZ P z s => intro σ; exact .iotaZ _ _ _
  | iotaS P z s n => intro σ; exact .iotaS _ _ _ _
  | piL _ ih => intro σ; exact .piL (ih σ)
  | piR _ ih => intro σ; exact .piR (ih _)
  | lam _ ih => intro σ; exact .lam (ih _)
  | appL _ ih => intro σ; exact .appL (ih σ)
  | appR _ ih => intro σ; exact .appR (ih σ)
  | succ _ ih => intro σ; exact .succ (ih σ)
  | recP _ ih => intro σ; exact .recP (ih σ)
  | recZ _ ih => intro σ; exact .recZ (ih σ)
  | recS _ ih => intro σ; exact .recS (ih σ)
  | recN _ ih => intro σ; exact .recN (ih σ)

theorem Reds.subst {a b} (h : Reds a b) (σ : Nat → Tm) :
    Reds (Proto.Kernel.subst σ a) (Proto.Kernel.subst σ b) :=
  Star.lift (Proto.Kernel.subst σ) (fun _ _ r => r.subst σ) h

theorem Conv.subst {a b} (h : Conv a b) (σ : Nat → Tm) :
    Conv (Proto.Kernel.subst σ a) (Proto.Kernel.subst σ b) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨Proto.Kernel.subst σ c, h1.subst σ, h2.subst σ⟩

/-! ## Reducts keep the head constructor -/

theorem Reds.pi_inv {A B t} (h : Reds (Tm.pi A B) t) :
    ∃ A' B', t = Tm.pi A' B' ∧ Reds A A' ∧ Reds B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl _, .refl _⟩
  | tail _ r ih =>
      obtain ⟨A', B', rfl, h1, h2⟩ := ih
      cases r with
      | piL r => exact ⟨_, _, rfl, .tail h1 r, h2⟩
      | piR r => exact ⟨_, _, rfl, h1, .tail h2 r⟩

theorem Reds.sort_inv {n t} (h : Reds (Tm.sort n) t) : t = Tm.sort n := by
  induction h with
  | refl => rfl
  | tail _ r ih => subst ih; cases r

theorem Reds.nat_inv {t} (h : Reds Tm.nat t) : t = Tm.nat := by
  induction h with
  | refl => rfl
  | tail _ r ih => subst ih; cases r

theorem Conv.pi_inj {A A' B B'} (h : Conv (Tm.pi A B) (Tm.pi A' B')) :
    Conv A A' ∧ Conv B B' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨C, D, rfl, a1, b1⟩ := h1.pi_inv
  obtain ⟨C', D', e, a2, b2⟩ := h2.pi_inv
  cases e
  exact ⟨⟨_, a1, a2⟩, ⟨_, b1, b2⟩⟩

theorem Conv.sort_inj {n m} (h : Conv (Tm.sort n) (Tm.sort m)) : n = m := by
  obtain ⟨c, h1, h2⟩ := h
  have := h1.sort_inv; subst this
  have := h2.sort_inv; cases this; rfl

theorem Conv.pi_ne_sort {A B n} (h : Conv (Tm.pi A B) (Tm.sort n)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨_, _, rfl, _, _⟩ := h1.pi_inv
  cases h2.sort_inv

theorem Conv.nat_ne_pi {A B} (h : Conv Tm.nat (Tm.pi A B)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨_, _, rfl, _, _⟩ := h2.pi_inv
  cases h1.nat_inv

theorem Conv.nat_ne_sort {n} (h : Conv Tm.nat (Tm.sort n)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  have := h1.nat_inv; subst this
  cases h2.sort_inv

end Proto.Kernel
