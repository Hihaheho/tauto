import Proto.Nib.Typing

/-!
# A place in a typing derivation, and what may fill it

`docs/design/macro-semantics.md`, T5, for executable code, the typing
half. `Spot D e Γ' B σ fill` says: the derivation `D` of a term `t` has a node
`Γ' ⊢ e : B ! σ`, and `t = fill e`. It is the position `⊢ C[e] ok`,
`Γ ⊢ e : A ! ε` of T5 as a place in the derivation, so that nothing has to be
said about which of the (many) derivations of a term is meant.

`Spot.replace` is T5's typing half: a term `e'` of the same type at a row
inside the node's row can be put in the place, and the whole is typed as
before, at the same type and row. The rows and types of the nodes above the
place do not move, so the side conditions of `handle` and the like, which
talk about them, are kept.

The forms a program writes are covered. The run-time forms (`loc`, `run`,
`info`, `select`) are not: a macro is expanded before anything runs. A place
inside a value that is given a tag (`tagged`) needs the filled term to be a
value, which the frame asks for.
-/

namespace Proto.Nib

mutual
  inductive Spot : ∀ {sg : Sig} {S Γ : Ctx} {t : Tm} {A : Ty} {ρ : Row},
      HasType sg S Γ t A ρ → Tm → Ctx → Ty → Row → (Tm → Tm) → Prop where
    | here {sg S Γ t A ρ} (D : HasType sg S Γ t A ρ) : Spot D t Γ A ρ id
    | lam {sg S Γ ps body A ρ e Γ' B σ fill} (h : HasType sg S (ps ++ Γ) body A ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.lam h) e Γ' B σ (fun x => .lam ps (fill x))
    | appF {sg S Γ f args ps A ρf ρa ρ e Γ' B σ fill}
        (hf : HasType sg S Γ f (.fn ps A ρ) ρf) (ha : HasTypes sg S Γ args ps ρa) :
        Spot hf e Γ' B σ fill →
        Spot (HasType.app hf ha) e Γ' B σ (fun x => .app (fill x) args)
    | appA {sg S Γ f args ps A ρf ρa ρ e Γ' B σ fill}
        (hf : HasType sg S Γ f (.fn ps A ρ) ρf) (ha : HasTypes sg S Γ args ps ρa) :
        Spots ha e Γ' B σ fill →
        Spot (HasType.app hf ha) e Γ' B σ (fun x => .app f (fill x))
    | iteC {sg S Γ c t f A ρc ρt ρf e Γ' B σ fill}
        (hc : HasType sg S Γ c .bool ρc) (ht : HasType sg S Γ t A ρt) (hf : HasType sg S Γ f A ρf) :
        Spot hc e Γ' B σ fill →
        Spot (HasType.ite hc ht hf) e Γ' B σ (fun x => .ite (fill x) t f)
    | iteT {sg S Γ c t f A ρc ρt ρf e Γ' B σ fill}
        (hc : HasType sg S Γ c .bool ρc) (ht : HasType sg S Γ t A ρt) (hf : HasType sg S Γ f A ρf) :
        Spot ht e Γ' B σ fill →
        Spot (HasType.ite hc ht hf) e Γ' B σ (fun x => .ite c (fill x) f)
    | iteF {sg S Γ c t f A ρc ρt ρf e Γ' B σ fill}
        (hc : HasType sg S Γ c .bool ρc) (ht : HasType sg S Γ t A ρt) (hf : HasType sg S Γ f A ρf) :
        Spot hf e Γ' B σ fill →
        Spot (HasType.ite hc ht hf) e Γ' B σ (fun x => .ite c t (fill x))
    | cell {sg S Γ init A ρ e Γ' B σ fill} (h : HasType sg S Γ init A ρ) (hd : DivClosed sg A) :
        Spot h e Γ' B σ fill →
        Spot (HasType.cell h hd) e Γ' B σ (fun x => .cell A (fill x))
    | fresh {sg S Γ init A ρ e Γ' B σ fill} (h : HasType sg S Γ init A ρ) (hd : DivClosed sg A) :
        Spot h e Γ' B σ fill →
        Spot (HasType.fresh h hd) e Γ' B σ (fun x => .fresh A (fill x))
    | get {sg S Γ c A ρ e Γ' B σ fill} (h : HasType sg S Γ c (.cell A) ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.get h) e Γ' B σ (fun x => .get (fill x))
    | setC {sg S Γ c v A ρc ρv e Γ' B σ fill}
        (hc : HasType sg S Γ c (.cell A) ρc) (hv : HasType sg S Γ v A ρv) :
        Spot hc e Γ' B σ fill →
        Spot (HasType.set hc hv) e Γ' B σ (fun x => .set (fill x) v)
    | setV {sg S Γ c v A ρc ρv e Γ' B σ fill}
        (hc : HasType sg S Γ c (.cell A) ρc) (hv : HasType sg S Γ v A ρv) :
        Spot hv e Γ' B σ fill →
        Spot (HasType.set hc hv) e Γ' B σ (fun x => .set c (fill x))
    | tag {sg S Γ a t A ρ e Γ' B σ fill} (h : HasType sg S Γ t A ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.tag (a := a) h) e Γ' B σ (fun x => .tag a (fill x))
    | con {sg S Γ d args c fields cs F ρ e Γ' B σ fill}
        (hd : sg.data d = some cs) (hc : cs[c]? = some F)
        (h : HasTypes sg S Γ fields (fieldsOf F args) ρ) :
        Spots h e Γ' B σ fill →
        Spot (HasType.con hd hc h) e Γ' B σ (fun x => .con d args c (fill x))
    | proj {sg S Γ i t d args F B₀ ρ e Γ' B σ fill}
        (hd : sg.data d = some [F]) (hi : F[i]? = some B₀) (h : HasType sg S Γ t (.data d args) ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.proj hd hi h) e Γ' B σ (fun x => .proj i (fill x))
    | perform {sg S Γ ev args ps R ρa e Γ' B σ fill}
        (ho : sg.op ev = some (ps, R)) (h : HasTypes sg S Γ args ps ρa) :
        Spots h e Γ' B σ fill →
        Spot (HasType.perform ho h) e Γ' B σ (fun x => .perform ev (fill x))
    | handleRetBody {sg S Γ body ret clauses B₀ T ρb ρr ρ e Γ' B σ fill}
        (hb : HasType sg S Γ body B₀ ρb) (hr : HasType sg S (B₀ :: Γ) ret T ρr)
        (hs : Row.Sub ρr ρ) (hcov : ∀ ev, ev ∈ ρb → Covers sg clauses ev ∨ ev ∈ ρ)
        (hcl : ∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c) :
        Spot hb e Γ' B σ fill →
        Spot (HasType.handleRet hb hr hs hcov hcl) e Γ' B σ
          (fun x => .handle (fill x) (some ret) clauses)
    | handleRetRet {sg S Γ body ret clauses B₀ T ρb ρr ρ e Γ' B σ fill}
        (hb : HasType sg S Γ body B₀ ρb) (hr : HasType sg S (B₀ :: Γ) ret T ρr)
        (hs : Row.Sub ρr ρ) (hcov : ∀ ev, ev ∈ ρb → Covers sg clauses ev ∨ ev ∈ ρ)
        (hcl : ∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c) :
        Spot hr e Γ' B σ fill →
        Spot (HasType.handleRet hb hr hs hcov hcl) e Γ' B σ
          (fun x => .handle body (some (fill x)) clauses)
    | handleRetClause {sg S Γ body ret clauses B₀ T ρb ρr ρ e Γ' B σ fill pre post c}
        (hb : HasType sg S Γ body B₀ ρb) (hr : HasType sg S (B₀ :: Γ) ret T ρr)
        (hs : Row.Sub ρr ρ) (hcov : ∀ ev, ev ∈ ρb → Covers sg clauses ev ∨ ev ∈ ρ)
        (hcl : ∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c)
        (hsplit : clauses = pre ++ c :: post) (hc : ClauseOk sg S Γ T ρ c) :
        SpotC hc e Γ' B σ fill →
        Spot (HasType.handleRet hb hr hs hcov hcl) e Γ' B σ
          (fun x => .handle body (some ret) (pre ++ fill x :: post))
    | handleBody {sg S Γ body clauses B₀ T ρb ρ e Γ' B σ fill}
        (hb : HasType sg S Γ body B₀ ρb) (hf : Fits B₀ T)
        (hcov : ∀ ev, ev ∈ ρb → Covers sg clauses ev ∨ ev ∈ ρ)
        (hcl : ∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c) :
        Spot hb e Γ' B σ fill →
        Spot (HasType.handle hb hf hcov hcl) e Γ' B σ (fun x => .handle (fill x) none clauses)
    | handleClause {sg S Γ body clauses B₀ T ρb ρ e Γ' B σ fill pre post c}
        (hb : HasType sg S Γ body B₀ ρb) (hf : Fits B₀ T)
        (hcov : ∀ ev, ev ∈ ρb → Covers sg clauses ev ∨ ev ∈ ρ)
        (hcl : ∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c)
        (hsplit : clauses = pre ++ c :: post) (hc : ClauseOk sg S Γ T ρ c) :
        SpotC hc e Γ' B σ fill →
        Spot (HasType.handle hb hf hcov hcl) e Γ' B σ
          (fun x => .handle body none (pre ++ fill x :: post))
    | brw {sg S Γ t A ρ e Γ' B σ fill} (h : HasType sg S Γ t (.cell A) ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.brw h) e Γ' B σ (fun x => .brw (fill x))
    | mbrw {sg S Γ t A ρ e Γ' B σ fill} (h : HasType sg S Γ t (.cell A) ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.mbrw h) e Γ' B σ (fun x => .mbrw (fill x))
    | field {sg S Γ i b d args F B₀ ρ e Γ' B σ fill}
        (hd : sg.data d = some [F]) (hi : F[i]? = some B₀) (h : HasType sg S Γ b (.brw (.data d args)) ρ) :
        Spot h e Γ' B σ fill →
        Spot (HasType.field hd hi h) e Γ' B σ (fun x => .field i (fill x))
    | writeB {sg S Γ b v A ρb ρv e Γ' B σ fill}
        (hb : HasType sg S Γ b (.mbrw A) ρb) (hv : HasType sg S Γ v A ρv) :
        Spot hb e Γ' B σ fill →
        Spot (HasType.write hb hv) e Γ' B σ (fun x => .write (fill x) v)
    | writeV {sg S Γ b v A ρb ρv e Γ' B σ fill}
        (hb : HasType sg S Γ b (.mbrw A) ρb) (hv : HasType sg S Γ v A ρv) :
        Spot hv e Γ' B σ fill →
        Spot (HasType.write hb hv) e Γ' B σ (fun x => .write b (fill x))
    | weaken {sg S Γ t A ρ ρ' e Γ' B σ fill} (h : HasType sg S Γ t A ρ) (hs : Row.Sub ρ ρ') :
        Spot h e Γ' B σ fill → Spot (HasType.weaken h hs) e Γ' B σ fill
    | fits {sg S Γ t A T ρ e Γ' B σ fill} (h : HasType sg S Γ t A ρ) (hf : Fits A T) :
        Spot h e Γ' B σ fill → Spot (HasType.fits h hf) e Γ' B σ fill
    | tagged {sg S Γ t A ρ e Γ' B σ fill} {a : Nat} (hv : Value t) (h : HasType sg S Γ t A ρ)
        (hvf : ∀ x, Value (fill x)) :
        Spot h e Γ' B σ fill → Spot (HasType.tagged (a := a) hv h) e Γ' B σ fill

  /-- The same for the arguments of a call, a constructor or an operation. -/
  inductive Spots : ∀ {sg : Sig} {S Γ : Ctx} {ts : List Tm} {As : List Ty} {ρ : Row},
      HasTypes sg S Γ ts As ρ → Tm → Ctx → Ty → Row → (Tm → List Tm) → Prop where
    | head {sg S Γ t ts A As ρ ρs e Γ' B σ fill}
        (h : HasType sg S Γ t A ρ) (hs : HasTypes sg S Γ ts As ρs) :
        Spot h e Γ' B σ fill →
        Spots (HasTypes.cons h hs) e Γ' B σ (fun x => fill x :: ts)
    | tail {sg S Γ t ts A As ρ ρs e Γ' B σ fill}
        (h : HasType sg S Γ t A ρ) (hs : HasTypes sg S Γ ts As ρs) :
        Spots hs e Γ' B σ fill →
        Spots (HasTypes.cons h hs) e Γ' B σ (fun x => t :: fill x)

  /-- The same for an arm of a handler. -/
  inductive SpotC : ∀ {sg : Sig} {S Γ : Ctx} {T : Ty} {ρ : Row} {c : Clause},
      ClauseOk sg S Γ T ρ c → Tm → Ctx → Ty → Row → (Tm → Clause) → Prop where
    | body {sg S Γ T ρ ev pats bd ps R Δ ρa A e Γ' B σ fill}
        (ho : sg.op ev = some (ps, R)) (hp : PatsOk sg pats (ps ++ [.fn [R] T ρ]) Δ)
        (h : HasType sg S (Δ ++ Γ) bd A ρa) (hf : Fits A T) (hs : Row.Sub ρa ρ) :
        Spot h e Γ' B σ fill →
        SpotC (ClauseOk.mk ho hp h hf hs) e Γ' B σ (fun x => .mk ev pats none (fill x))
    | gBody {sg S Γ T ρ ev pats g bd ps R Δ ρa A e Γ' B σ fill}
        (ho : sg.op ev = some (ps, R)) (hp : PatsOk sg pats (ps ++ [.fn [R] T ρ]) Δ)
        (hg : HasType sg S (Δ ++ Γ) g .bool []) (h : HasType sg S (Δ ++ Γ) bd A ρa)
        (hf : Fits A T) (hs : Row.Sub ρa ρ) :
        Spot h e Γ' B σ fill →
        SpotC (ClauseOk.guarded ho hp hg h hf hs) e Γ' B σ
          (fun x => .mk ev pats (some g) (fill x))
    | gGuard {sg S Γ T ρ ev pats g bd ps R Δ ρa A e Γ' B σ fill}
        (ho : sg.op ev = some (ps, R)) (hp : PatsOk sg pats (ps ++ [.fn [R] T ρ]) Δ)
        (hg : HasType sg S (Δ ++ Γ) g .bool []) (h : HasType sg S (Δ ++ Γ) bd A ρa)
        (hf : Fits A T) (hs : Row.Sub ρa ρ) :
        Spot hg e Γ' B σ fill →
        SpotC (ClauseOk.guarded ho hp hg h hf hs) e Γ' B σ
          (fun x => .mk ev pats (some (fill x)) bd)
end



/-- An arm that keeps its operation, its patterns and whether it has a guard
takes what the arm it stands for takes. -/
theorem Covers.swap_clause {sg : Sig} {pre post : List Clause} {c c' : Clause} {e : Eff}
    (h1 : c'.eff = c.eff) (h2 : c'.guard = none ↔ c.guard = none) (h3 : c'.pats = c.pats)
    (h : Covers sg (pre ++ c :: post) e) : Covers sg (pre ++ c' :: post) e := by
  obtain ⟨ps, R, he, hall⟩ := h
  refine ⟨ps, R, he, fun vs k hi => ?_⟩
  obtain ⟨c0, hm, h4, h5, h6⟩ := hall vs k hi
  by_cases hc0 : c0 = c
  · subst hc0
    exact ⟨c', by simp, by rw [h1, h4], h2.mpr h5, by rw [h3]; exact h6⟩
  · refine ⟨c0, ?_, h4, h5, h6⟩
    rcases List.mem_append.mp hm with h7 | h7
    · exact List.mem_append.mpr (Or.inl h7)
    · rcases List.mem_cons.mp h7 with h8 | h8
      · exact absurd h8 hc0
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h8))

/-- What the frame of an arm fills in keeps its shape. -/
theorem SpotC.shape {sg : Sig} {S Γ : Ctx} {T : Ty} {ρ : Row} {c : Clause}
    {D : ClauseOk sg S Γ T ρ c} {e : Tm} {Γ' : Ctx} {B : Ty} {σ : Row} {fill : Tm → Clause}
    (F : SpotC D e Γ' B σ fill) (x : Tm) :
    (fill x).eff = c.eff ∧ ((fill x).guard = none ↔ c.guard = none) ∧ (fill x).pats = c.pats := by
  cases F <;> simp [Clause.eff, Clause.guard, Clause.pats]

variable {sg : Sig} {S : Ctx}

mutual
  /-- T5, typing half: what fills the place keeps the term typed, at the same
  type and row, if it has the node's type and a row inside the node's. -/
  theorem Spot.replace {Γ : Ctx} {t : Tm} {A : Ty} {ρ : Row} {D : HasType sg S Γ t A ρ}
      {e : Tm} {Γ' : Ctx} {B : Ty} {σ : Row} {fill : Tm → Tm}
      (F : Spot D e Γ' B σ fill) {e' : Tm} {σ' : Row}
      (h' : HasType sg S Γ' e' B σ') (hs : Row.Sub σ' σ) :
      HasType sg S Γ (fill e') A ρ :=
    match F with
    | .here _ => HasType.weaken h' hs
    | .lam _ F => HasType.lam (F.replace h' hs)
    | .appF _ ha F => HasType.app (F.replace h' hs) ha
    | .appA hf _ F => HasType.app hf (F.replaceS h' hs)
    | .iteC _ ht hf F => HasType.ite (F.replace h' hs) ht hf
    | .iteT hc _ hf F => HasType.ite hc (F.replace h' hs) hf
    | .iteF hc ht _ F => HasType.ite hc ht (F.replace h' hs)
    | .cell _ hd F => HasType.cell (F.replace h' hs) hd
    | .fresh _ hd F => HasType.fresh (F.replace h' hs) hd
    | .get _ F => HasType.get (F.replace h' hs)
    | .setC _ hv F => HasType.set (F.replace h' hs) hv
    | .setV hc _ F => HasType.set hc (F.replace h' hs)
    | .tag _ F => HasType.tag (F.replace h' hs)
    | .con hd hc _ F => HasType.con hd hc (F.replaceS h' hs)
    | .proj hd hi _ F => HasType.proj hd hi (F.replace h' hs)
    | .perform ho _ F => HasType.perform ho (F.replaceS h' hs)
    | .handleRetBody _ hr hsr hcov hcl F => HasType.handleRet (F.replace h' hs) hr hsr hcov hcl
    | .handleRetRet hb _ hsr hcov hcl F => HasType.handleRet hb (F.replace h' hs) hsr hcov hcl
    | .handleRetClause hb hr hsr hcov hcl hsplit hc F =>
        HasType.handleRet hb hr hsr (by
          subst hsplit
          intro ev hev
          rcases hcov ev hev with h1 | h1
          · exact Or.inl (Covers.swap_clause (F.shape e').1 (F.shape e').2.1 (F.shape e').2.2 h1)
          · exact Or.inr h1) (by
          subst hsplit
          intro c hc'
          rcases List.mem_append.mp hc' with h1 | h1
          · exact hcl c (List.mem_append.mpr (Or.inl h1))
          · rcases List.mem_cons.mp h1 with h2 | h2
            · subst h2; exact F.replaceC h' hs
            · exact hcl c (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h2))))
    | .handleBody _ hf hcov hcl F => HasType.handle (F.replace h' hs) hf hcov hcl
    | .handleClause hb hf hcov hcl hsplit hc F =>
        HasType.handle hb hf (by
          subst hsplit
          intro ev hev
          rcases hcov ev hev with h1 | h1
          · exact Or.inl (Covers.swap_clause (F.shape e').1 (F.shape e').2.1 (F.shape e').2.2 h1)
          · exact Or.inr h1) (by
          subst hsplit
          intro c hc'
          rcases List.mem_append.mp hc' with h1 | h1
          · exact hcl c (List.mem_append.mpr (Or.inl h1))
          · rcases List.mem_cons.mp h1 with h2 | h2
            · subst h2; exact F.replaceC h' hs
            · exact hcl c (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h2))))
    | .brw _ F => HasType.brw (F.replace h' hs)
    | .mbrw _ F => HasType.mbrw (F.replace h' hs)
    | .field hd hi _ F => HasType.field hd hi (F.replace h' hs)
    | .writeB _ hv F => HasType.write (F.replace h' hs) hv
    | .writeV hb _ F => HasType.write hb (F.replace h' hs)
    | .weaken _ hsr F => HasType.weaken (F.replace h' hs) hsr
    | .fits _ hf F => HasType.fits (F.replace h' hs) hf
    | .tagged _ _ hvf F => HasType.tagged (hvf e') (F.replace h' hs)

  theorem Spots.replaceS {Γ : Ctx} {ts : List Tm} {As : List Ty} {ρ : Row}
      {D : HasTypes sg S Γ ts As ρ} {e : Tm} {Γ' : Ctx} {B : Ty} {σ : Row} {fill : Tm → List Tm}
      (F : Spots D e Γ' B σ fill) {e' : Tm} {σ' : Row}
      (h' : HasType sg S Γ' e' B σ') (hs : Row.Sub σ' σ) :
      HasTypes sg S Γ (fill e') As ρ :=
    match F with
    | .head _ hs' F => HasTypes.cons (F.replace h' hs) hs'
    | .tail h _ F => HasTypes.cons h (F.replaceS h' hs)

  theorem SpotC.replaceC {Γ : Ctx} {T : Ty} {ρ : Row} {c : Clause}
      {D : ClauseOk sg S Γ T ρ c} {e : Tm} {Γ' : Ctx} {B : Ty} {σ : Row} {fill : Tm → Clause}
      (F : SpotC D e Γ' B σ fill) {e' : Tm} {σ' : Row}
      (h' : HasType sg S Γ' e' B σ') (hs : Row.Sub σ' σ) :
      ClauseOk sg S Γ T ρ (fill e') :=
    match F with
    | .body ho hp _ hf hsr F => ClauseOk.mk ho hp (F.replace h' hs) hf hsr
    | .gBody ho hp hg _ hf hsr F => ClauseOk.guarded ho hp hg (F.replace h' hs) hf hsr
    | .gGuard ho hp _ h hf hsr F => ClauseOk.guarded ho hp (F.replace h' hs) h hf hsr
end

end Proto.Nib
