/- Pure reference semantics for `cnf::to_cnf`/`cnf::eval_cnf`, and the specs connecting
them to the extracted `cnf.to_cnf`/`cnf.eval_cnf`. `to_cnf` is a single recursive pass
parametrized by a polarity flag (`negate`) that pushes negations to literals and swaps
AND/OR (De Morgan) simultaneously -- no auxiliary variables are introduced, so it's
logically *equivalent* to its input, not just equisatisfiable, which is what makes an
unconditional structural-induction correctness proof possible. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-! ### Pure semantics -/

/-- A literal is true under `w` iff it's the (possibly negated) value `w` assigns its
    variable. -/
def Literal.eval (w : Std.U8 → Bool) (lit : cnf.Literal) : Bool :=
  if lit.negated then !w lit.var else w lit.var

/-- A clause (disjunction of literals) is true iff some literal in it is. -/
def Clause.eval (w : Std.U8 → Bool) (clause : List cnf.Literal) : Bool :=
  clause.any (Literal.eval w)

/-- A CNF (conjunction of clauses) is true iff every clause in it is. -/
def Cnf.eval (w : Std.U8 → Bool) (cnf : List (List cnf.Literal)) : Bool :=
  cnf.all (Clause.eval w)

/-- The variables occurring in a clause, as a list (mirrors `varsOf`). -/
def clauseVars (c : List cnf.Literal) : List Std.U8 := c.map cnf.Literal.var

/-- The variables occurring anywhere in a CNF, as a list (mirrors `varsOf`). -/
def cnfVars (c : List (List cnf.Literal)) : List Std.U8 := c.flatMap clauseVars

@[simp]
theorem clauseVars_append (c1 c2 : List cnf.Literal) :
    clauseVars (c1 ++ c2) = clauseVars c1 ++ clauseVars c2 := by simp [clauseVars]

@[simp]
theorem cnfVars_append (c1 c2 : List (List cnf.Literal)) :
    cnfVars (c1 ++ c2) = cnfVars c1 ++ cnfVars c2 := by simp [cnfVars]

/-- Unwraps a `cnf.Cnf`'s `Vec`-of-`Vec` representation down to a plain `List (List
    Literal)`, matching `cnfPure`/`distributeList`/`Cnf.eval`'s pure representation.
    Every extraction-layer spec below is phrased in terms of this, since the raw
    `.val` of a `cnf.Cnf` is a `List cnf.Clause` (still `Vec`-wrapped clauses). -/
def Cnf.contents (c : cnf.Cnf) : List (List cnf.Literal) := c.val.map (fun cl => cl.val)

@[simp]
theorem Cnf.contents_def (c : cnf.Cnf) : Cnf.contents c = c.val.map (fun cl => cl.val) := rfl

@[simp]
theorem Clause.eval_append (w : Std.U8 → Bool) (c1 c2 : List cnf.Literal) :
    Clause.eval w (c1 ++ c2) = (Clause.eval w c1 || Clause.eval w c2) := by
  simp [Clause.eval, List.any_append]

@[simp]
theorem Cnf.eval_append (w : Std.U8 → Bool) (c1 c2 : List (List cnf.Literal)) :
    Cnf.eval w (c1 ++ c2) = (Cnf.eval w c1 && Cnf.eval w c2) := by
  simp [Cnf.eval, List.all_append]

/-- `∀x∈l, (p || q x) ↔ p || (∀x∈l, q x)` -- always true, even for `l = []` (both sides
    reduce to `p` there). Used to push a `Clause.eval` fact out of a `List.map` inside a
    `Cnf.eval`. -/
theorem Cnf.eval_or_distrib (p : Bool) (l : List α) (q : α → Bool) :
    (l.all (fun x => p || q x)) = (p || l.all q) := by
  induction l with
  | nil => simp
  | cons a tl ih => cases p <;> simp_all

/-- Pure reference semantics for `cnf::distribute`: the cross join of two clause lists,
    unioning every pair. -/
def distributeList (c1 c2 : List (List cnf.Literal)) : List (List cnf.Literal) :=
  c1.flatMap (fun cl1 => c2.map (fun cl2 => cl1 ++ cl2))

@[simp]
theorem mem_distributeList {c1 c2 : List (List cnf.Literal)} {cl : List cnf.Literal} :
    cl ∈ distributeList c1 c2 ↔ ∃ cl1 ∈ c1, ∃ cl2 ∈ c2, cl = cl1 ++ cl2 := by
  simp only [distributeList, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨cl1, hcl1, cl2, hcl2, rfl⟩
    exact ⟨cl1, hcl1, cl2, hcl2, rfl⟩
  · rintro ⟨cl1, hcl1, cl2, hcl2, rfl⟩
    exact ⟨cl1, hcl1, cl2, hcl2, rfl⟩

theorem distributeList_length (c1 c2 : List (List cnf.Literal)) :
    (distributeList c1 c2).length = c1.length * c2.length := by
  induction c1 with
  | nil => simp [distributeList]
  | cons cl1 rest ih =>
    simp only [distributeList, List.flatMap_cons] at ih ⊢
    rw [List.length_append, List.length_map, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem mem_cnfVars_distributeList {c1 c2 : List (List cnf.Literal)} {k : Std.U8}
    (hk : k ∈ cnfVars (distributeList c1 c2)) : k ∈ cnfVars c1 ∨ k ∈ cnfVars c2 := by
  simp only [cnfVars, distributeList, List.mem_flatMap, List.mem_map] at hk
  obtain ⟨cl, ⟨cl1, hcl1, cl2, hcl2, rfl⟩, hkcl⟩ := hk
  simp only [clauseVars_append, List.mem_append] at hkcl
  rcases hkcl with hkcl | hkcl
  · exact Or.inl (List.mem_flatMap.mpr ⟨cl1, hcl1, hkcl⟩)
  · exact Or.inr (List.mem_flatMap.mpr ⟨cl2, hcl2, hkcl⟩)

/-- Mapping "union with `cl1`" over a clause list, then checking the whole CNF, is the same
    as ORing `cl1` itself against the original CNF: every produced clause is satisfied iff
    `cl1` is (which makes all of them satisfied) or the original clause was (pointwise). -/
theorem Cnf.eval_map_append (w : Std.U8 → Bool) (cl1 : List cnf.Literal)
    (c2 : List (List cnf.Literal)) :
    Cnf.eval w (c2.map (fun cl2 => cl1 ++ cl2)) = (Clause.eval w cl1 || Cnf.eval w c2) := by
  simp only [Cnf.eval, List.all_map, Function.comp_def, Clause.eval_append]
  exact Cnf.eval_or_distrib (Clause.eval w cl1) c2 (Clause.eval w)

/-- `distribute` implements OR: it's true exactly when *either* side's CNF is. -/
theorem Cnf.eval_distributeList (w : Std.U8 → Bool) (c1 c2 : List (List cnf.Literal)) :
    Cnf.eval w (distributeList c1 c2) = (Cnf.eval w c1 || Cnf.eval w c2) := by
  induction c1 with
  | nil => simp [distributeList, Cnf.eval]
  | cons cl1 rest ih =>
    simp only [distributeList] at ih ⊢
    rw [List.flatMap_cons, Cnf.eval_append, Cnf.eval_map_append, ih]
    simp only [Cnf.eval, List.all_cons]
    cases h1 : Clause.eval w cl1 <;> cases h2 : Cnf.eval w rest <;> cases h3 : Cnf.eval w c2 <;>
      simp_all

/-- Pure reference semantics for `cnf::cnf_rec`: pushes negations to literals and
    distributes OR over AND, guided by the polarity flag `negate`. -/
def cnfPure : expr.Expr → Bool → List (List cnf.Literal)
  | .True, negate => if negate then [[]] else []
  | .False, negate => if negate then [] else [[]]
  | .Variable v, negate => [[⟨v, negate⟩]]
  | .Conj e1 e2, false => cnfPure e1 false ++ cnfPure e2 false
  | .Conj e1 e2, true => distributeList (cnfPure e1 true) (cnfPure e2 true)
  | .Disj e1 e2, false => distributeList (cnfPure e1 false) (cnfPure e2 false)
  | .Disj e1 e2, true => cnfPure e1 true ++ cnfPure e2 true
  | .Neg e, negate => cnfPure e (!negate)

/-- Classic worst-case CNF blowup bound: the number of clauses produced is at most
    exponential in `e`'s AST size. Used only to bound `Usize.max` overflow side
    conditions in `cnf_rec`'s proof (never as a tightness claim). -/
theorem cnfPure_length_le (e : expr.Expr) (negate : Bool) :
    (cnfPure e negate).length ≤ 2 ^ exprSize e := by
  induction e generalizing negate with
  | True => cases negate <;> simp [cnfPure, exprSize]
  | False => cases negate <;> simp [cnfPure, exprSize]
  | Variable v => cases negate <;> simp [cnfPure, exprSize]
  | Conj e1 e2 ih1 ih2 =>
    cases negate with
    | false =>
      simp only [cnfPure, exprSize, List.length_append]
      calc (cnfPure e1 false).length + (cnfPure e2 false).length
          ≤ 2 ^ exprSize e1 + 2 ^ exprSize e2 := Nat.add_le_add (ih1 false) (ih2 false)
        _ ≤ 2 ^ (exprSize e1 + exprSize e2) + 2 ^ (exprSize e1 + exprSize e2) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _))
        _ = 2 ^ (exprSize e1 + exprSize e2 + 1) := by rw [Nat.pow_succ]; ring
        _ ≤ 2 ^ (exprSize e1 + exprSize e2 + 1) := le_refl _
    | true =>
      simp only [cnfPure, exprSize, distributeList_length]
      calc (cnfPure e1 true).length * (cnfPure e2 true).length
          ≤ 2 ^ exprSize e1 * 2 ^ exprSize e2 := Nat.mul_le_mul (ih1 true) (ih2 true)
        _ = 2 ^ (exprSize e1 + exprSize e2) := (Nat.pow_add 2 (exprSize e1) (exprSize e2)).symm
        _ ≤ 2 ^ (exprSize e1 + exprSize e2 + 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  | Disj e1 e2 ih1 ih2 =>
    cases negate with
    | true =>
      simp only [cnfPure, exprSize, List.length_append]
      calc (cnfPure e1 true).length + (cnfPure e2 true).length
          ≤ 2 ^ exprSize e1 + 2 ^ exprSize e2 := Nat.add_le_add (ih1 true) (ih2 true)
        _ ≤ 2 ^ (exprSize e1 + exprSize e2) + 2 ^ (exprSize e1 + exprSize e2) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _))
        _ = 2 ^ (exprSize e1 + exprSize e2 + 1) := by rw [Nat.pow_succ]; ring
    | false =>
      simp only [cnfPure, exprSize, distributeList_length]
      calc (cnfPure e1 false).length * (cnfPure e2 false).length
          ≤ 2 ^ exprSize e1 * 2 ^ exprSize e2 := Nat.mul_le_mul (ih1 false) (ih2 false)
        _ = 2 ^ (exprSize e1 + exprSize e2) := (Nat.pow_add 2 (exprSize e1) (exprSize e2)).symm
        _ ≤ 2 ^ (exprSize e1 + exprSize e2 + 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  | Neg e ih =>
    simp only [cnfPure, exprSize]
    exact le_trans (ih (!negate)) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))

/-- Every clause `cnf_rec` ever produces has at most one literal per AST node of `e`
    -- used only to bound `Usize.max` overflow side conditions for `clause_union`'s own
    internal length addition in `cnf_rec`'s proof. -/
theorem cnfPure_clause_length_le (e : expr.Expr) (negate : Bool) :
    ∀ cl ∈ cnfPure e negate, cl.length ≤ exprSize e := by
  induction e generalizing negate with
  | True => cases negate <;> simp [cnfPure, exprSize]
  | False => cases negate <;> simp [cnfPure, exprSize]
  | Variable v => cases negate <;> simp [cnfPure, exprSize]
  | Conj e1 e2 ih1 ih2 =>
    cases negate with
    | false =>
      simp only [cnfPure, exprSize, List.mem_append]
      rintro cl (hcl | hcl)
      · exact le_trans (ih1 false cl hcl)
          (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      · exact le_trans (ih2 false cl hcl)
          (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
    | true =>
      simp only [cnfPure, exprSize, mem_distributeList]
      rintro cl ⟨cl1, hcl1, cl2, hcl2, rfl⟩
      simp only [List.length_append]
      exact le_trans (Nat.add_le_add (ih1 true cl1 hcl1) (ih2 true cl2 hcl2)) (Nat.le_succ _)
  | Disj e1 e2 ih1 ih2 =>
    cases negate with
    | true =>
      simp only [cnfPure, exprSize, List.mem_append]
      rintro cl (hcl | hcl)
      · exact le_trans (ih1 true cl hcl)
          (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      · exact le_trans (ih2 true cl hcl)
          (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
    | false =>
      simp only [cnfPure, exprSize, mem_distributeList]
      rintro cl ⟨cl1, hcl1, cl2, hcl2, rfl⟩
      simp only [List.length_append]
      exact le_trans (Nat.add_le_add (ih1 false cl1 hcl1) (ih2 false cl2 hcl2)) (Nat.le_succ _)
  | Neg e ih =>
    simp only [cnfPure, exprSize]
    exact fun cl hcl => le_trans (ih (!negate) cl hcl) (by simp)

/-- Every variable `cnf_rec` ever mentions came from `e` itself. -/
theorem cnfVars_cnfPure_subset (e : expr.Expr) (negate : Bool) :
    ∀ k ∈ cnfVars (cnfPure e negate), k ∈ varsOf e := by
  induction e generalizing negate with
  | True => cases negate <;> simp [cnfPure, cnfVars, clauseVars]
  | False => cases negate <;> simp [cnfPure, cnfVars, clauseVars]
  | Variable v => cases negate <;> simp [cnfPure, cnfVars, clauseVars, varsOf]
  | Conj e1 e2 ih1 ih2 =>
    cases negate with
    | false =>
      simp only [cnfPure, cnfVars_append, List.mem_append, varsOf]
      rintro k (hk | hk)
      · exact Or.inl (ih1 false k hk)
      · exact Or.inr (ih2 false k hk)
    | true =>
      intro k hk
      simp only [cnfPure] at hk
      simp only [varsOf, List.mem_append]
      rcases mem_cnfVars_distributeList hk with hk | hk
      · exact Or.inl (ih1 true k hk)
      · exact Or.inr (ih2 true k hk)
  | Disj e1 e2 ih1 ih2 =>
    cases negate with
    | true =>
      simp only [cnfPure, cnfVars_append, List.mem_append, varsOf]
      rintro k (hk | hk)
      · exact Or.inl (ih1 true k hk)
      · exact Or.inr (ih2 true k hk)
    | false =>
      intro k hk
      simp only [cnfPure] at hk
      simp only [varsOf, List.mem_append]
      rcases mem_cnfVars_distributeList hk with hk | hk
      · exact Or.inl (ih1 false k hk)
      · exact Or.inr (ih2 false k hk)
  | Neg e ih =>
    simp only [cnfPure, varsOf]
    exact fun k hk => ih (!negate) k hk

/-- **Core correctness theorem**: `cnfPure` is a polarity-parametrized equivalence-
    preserving transform. With `negate = false` this says `to_cnf` preserves meaning
    exactly (not just satisfiability). -/
theorem Cnf.eval_cnfPure (e : expr.Expr) (w : Std.U8 → Bool) (negate : Bool) :
    Cnf.eval w (cnfPure e negate) = (evalPure w e != negate) := by
  induction e generalizing negate with
  | True => cases negate <;> simp [cnfPure, Cnf.eval, Clause.eval, evalPure]
  | False => cases negate <;> simp [cnfPure, Cnf.eval, Clause.eval, evalPure]
  | Variable v => cases negate <;> simp [cnfPure, Cnf.eval, Clause.eval, Literal.eval, evalPure]
  | Conj e1 e2 ih1 ih2 =>
    cases negate with
    | false => simp [cnfPure, evalPure, ih1, ih2]
    | true =>
      simp only [cnfPure, Cnf.eval_distributeList, ih1, ih2, evalPure]
      cases evalPure w e1 <;> cases evalPure w e2 <;> simp
  | Disj e1 e2 ih1 ih2 =>
    cases negate with
    | true => simp [cnfPure, evalPure, ih1, ih2]
    | false =>
      simp only [cnfPure, Cnf.eval_distributeList, ih1, ih2, evalPure]
      cases evalPure w e1 <;> cases evalPure w e2 <;> simp
  | Neg e ih =>
    simp only [cnfPure, ih, evalPure]
    cases negate <;> cases evalPure w e <;> simp

/-! ### Extraction-matching layer -/

/-- `cnf::Literal` is a plain pair of `Copy` scalars, so cloning it is the identity. -/
@[step]
theorem cnf.Literal.Insts.CoreCloneClone.clone.spec (self : cnf.Literal) :
    cnf.Literal.Insts.CoreCloneClone.clone self ⦃ (l : cnf.Literal) => l = self ⦄ := by
  unfold cnf.Literal.Insts.CoreCloneClone.clone
    core.U8.Insts.CoreCloneClone.clone core.Bool.Insts.CoreCloneClone.clone
  step*

/-- `clause_union_loop0`/`_loop1` share this exact body: clone each remaining literal
    from `iter` and push it onto `lits`, in order. Since `Literal`'s clone is the
    identity, the net effect is appending `iter`'s elements onto `lits`. -/
@[step]
theorem cnf.clause_union_loop0.spec (iter : core.slice.iter.Iter cnf.Literal)
    (lits : alloc.vec.Vec cnf.Literal)
    (hlen : lits.val.length + iter.val.length ≤ Usize.max) :
    cnf.clause_union_loop0 iter lits ⦃ (r : alloc.vec.Vec cnf.Literal) =>
      r.val = lits.val ++ iter.val ⦄ := by
  unfold cnf.clause_union_loop0
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

@[step]
theorem cnf.clause_union_loop1.spec (iter : core.slice.iter.Iter cnf.Literal)
    (lits : alloc.vec.Vec cnf.Literal)
    (hlen : lits.val.length + iter.val.length ≤ Usize.max) :
    cnf.clause_union_loop1 iter lits ⦃ (r : alloc.vec.Vec cnf.Literal) =>
      r.val = lits.val ++ iter.val ⦄ := by
  unfold cnf.clause_union_loop1
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::cnf::clause_union`**: unions two clauses by
    concatenation. -/
@[step]
theorem cnf.clause_union.spec (c1 c2 : cnf.Clause)
    (hlen : c1.val.length + c2.val.length ≤ Usize.max) :
    cnf.clause_union c1 c2 ⦃ (r : cnf.Clause) => r.val = c1.val ++ c2.val ⦄ := by
  unfold cnf.clause_union
  step*

/-- `conj_cnf_loop` pushes every remaining clause from `iter` onto `clauses`, in
    order (no cloning: `IntoIter` owns its elements outright). -/
@[step]
theorem cnf.conj_cnf_loop.spec (iter : alloc.vec.into_iter.IntoIter cnf.Clause)
    (clauses : alloc.vec.Vec cnf.Clause)
    (hlen : clauses.val.length + iter.val.length ≤ Usize.max) :
    cnf.conj_cnf_loop iter clauses ⦃ (r : alloc.vec.Vec cnf.Clause) =>
      r.val = clauses.val ++ iter.val ⦄ := by
  unfold cnf.conj_cnf_loop
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::cnf::conj_cnf`**: unions two CNFs by
    concatenation (this is exactly AND, since `Cnf.eval` is `all` over clauses). -/
@[step]
theorem cnf.conj_cnf.spec (c1 c2 : cnf.Cnf) (hlen : c1.val.length + c2.val.length ≤ Usize.max) :
    cnf.conj_cnf c1 c2 ⦃ (r : cnf.Cnf) => r.val = c1.val ++ c2.val ⦄ := by
  unfold cnf.conj_cnf alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  step*

/-- `distribute_loop0_loop0` unions `clause1` with every remaining clause from `iter`
    (in order) and pushes the result. -/
@[step]
theorem cnf.distribute_loop0_loop0.spec (iter : core.slice.iter.Iter cnf.Clause)
    (result : alloc.vec.Vec cnf.Clause) (clause1 : cnf.Clause)
    (hclause : ∀ clause2 ∈ iter.val, clause1.val.length + clause2.val.length ≤ Usize.max)
    (hlen : result.val.length + iter.val.length ≤ Usize.max) :
    cnf.distribute_loop0_loop0 iter result clause1 ⦃ (r : alloc.vec.Vec cnf.Clause) =>
      Cnf.contents r = Cnf.contents result ++ iter.val.map (fun clause2 => clause1.val ++ clause2.val) ⦄ := by
  unfold cnf.distribute_loop0_loop0
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      have hb := hclause e (by simp_all)
      simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => intro cl2 hcl2; exact hclause cl2 (by simp_all)
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- `distribute_loop0` distributes every remaining clause from `iter` (in order)
    against all of `c2`. -/
@[step]
theorem cnf.distribute_loop0.spec (iter : core.slice.iter.Iter cnf.Clause) (c2 : cnf.Cnf)
    (result : alloc.vec.Vec cnf.Clause)
    (hclause : ∀ clause1 ∈ iter.val, ∀ clause2 ∈ c2.val,
      clause1.val.length + clause2.val.length ≤ Usize.max)
    (hlen : result.val.length + iter.val.length * c2.val.length ≤ Usize.max) :
    cnf.distribute_loop0 iter c2 result ⦃ (r : alloc.vec.Vec cnf.Clause) =>
      Cnf.contents r = Cnf.contents result ++ distributeList (iter.val.map (·.val)) (Cnf.contents c2) ⦄ := by
  unfold cnf.distribute_loop0
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp [distributeList]
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      have hc1 : clause1 = e := by simp_all
      have hiter2 : iter2.val = c2.val := by rw [iter2_post, s_post]
      rw [hc1, hiter2]
      exact hclause e (by simp_all)
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      have : c2.val.length ≤ (es.length + 1) * c2.val.length := by
        rw [Nat.succ_mul]; exact Nat.le_add_left _ _
      scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => intro clause1 hclause1; exact hclause clause1 (by simp_all)
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      have hiter2 : iter2.val = c2.val := by rw [iter2_post, s_post]
      have hiter1 : iter1.val.length = es.length := o_post.2 ▸ rfl
      have hlen1 : result1.val.length = result.val.length + c2.val.length := by
        have h := congrArg List.length result1_post
        simp only [Cnf.contents_def, List.length_map, List.length_append, hiter2] at h
        exact h
      simp only [List.length_cons, Nat.succ_mul] at hlen
      rw [hlen1, hiter1]
      scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      have hc1 : clause1 = e := by simp_all
      have hiter2 : iter2.val = c2.val := by rw [iter2_post, s_post]
      have hiter1 : iter1.val = es := o_post.2
      rw [hc1, hiter2] at result1_post
      rw [r_post, result1_post, hiter1]
      simp only [distributeList, List.map_cons, List.flatMap_cons, List.map_map,
        Function.comp_def, Cnf.contents_def, List.append_assoc]
termination_by iter.val.length
decreasing_by
  rcases hiter : iter.val with _ | ⟨e, es⟩
  · simp_all
  · simp only [hiter] at o_post
    obtain ⟨-, hrest⟩ := o_post
    rw [hrest]
    exact Nat.lt_succ_self _

/-- **Spec theorem for `sat_solver::cnf::distribute`**: the full cross join of `c1`
    and `c2`, unioning every pair of clauses -- this is `distributeList`. -/
@[step]
theorem cnf.distribute.spec (c1 c2 : cnf.Cnf)
    (hclause : ∀ clause1 ∈ c1.val, ∀ clause2 ∈ c2.val,
      clause1.val.length + clause2.val.length ≤ Usize.max)
    (hlen : c1.val.length * c2.val.length ≤ Usize.max) :
    cnf.distribute c1 c2 ⦃ (r : cnf.Cnf) =>
      Cnf.contents r = distributeList (Cnf.contents c1) (Cnf.contents c2) ⦄ := by
  unfold cnf.distribute
  step*
  · simp_all
  · simp_all [Cnf.contents_def]

/-- **Spec theorem for `sat_solver::cnf::cnf_rec`**: matches `cnfPure`. The headroom
    hypothesis is the classic worst-case CNF blowup bound (`cnfPure_length_le`), which
    alone bounds every `Vec`/`Usize.max` side-condition below: both the pairwise
    clause-length bound needed by `clause_union` (via `cnfPure_clause_length_le` and
    `exprSize e ≤ 2 ^ exprSize e ≤ Usize.max`) and the clause-count bound needed by
    `conj_cnf`/`distribute` (since the accumulated result's length is *exactly*
    `(cnfPure e negate).length` by construction). -/
@[step]
theorem cnf.cnf_rec.spec (e : expr.Expr) (negate : Bool) (hbound : 2 ^ exprSize e ≤ Usize.max) :
    cnf.cnf_rec e negate ⦃ (r : cnf.Cnf) => Cnf.contents r = cnfPure e negate ⦄ := by
  have main : ∀ n e, exprSize e ≤ n → ∀ negate, 2 ^ exprSize e ≤ Usize.max →
      cnf.cnf_rec e negate ⦃ (r : cnf.Cnf) => Cnf.contents r = cnfPure e negate ⦄ := by
    intro n
    induction n with
    | zero => intro e he; exact absurd he (by cases e <;> simp [exprSize])
    | succ n ihn =>
      intro e he negate hbound
      cases e with
      | True =>
        unfold cnf.cnf_rec
        split
        · unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
            rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
          step*
          simp_all [cnfPure, Cnf.contents_def, Array.to_slice, Array.make]
        · step*
          simp_all [cnfPure]
      | False =>
        unfold cnf.cnf_rec
        split
        · step*
          simp_all [cnfPure]
        · unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
            rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
          step*
          simp_all [cnfPure, Cnf.contents_def, Array.to_slice, Array.make]
      | Variable v =>
        unfold cnf.cnf_rec
        unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
          rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
        step*
        simp_all [cnfPure, Cnf.contents_def, Array.to_slice, Array.make]
      | Conj e1 e2 =>
        unfold cnf.cnf_rec
        have hlt1 : exprSize e1 < exprSize (expr.Expr.Conj e1 e2) := by
          simp only [exprSize]; exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
        have hlt2 : exprSize e2 < exprSize (expr.Expr.Conj e1 e2) := by
          simp only [exprSize]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
        have hn1 : exprSize e1 ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le hlt1 he)
        have hn2 : exprSize e2 ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le hlt2 he)
        have hbound1 : 2 ^ exprSize e1 ≤ Usize.max :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hlt1.le) hbound
        have hbound2 : 2 ^ exprSize e2 ≤ Usize.max :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hlt2.le) hbound
        split
        · have ih1 := ihn e1 hn1 true hbound1
          have ih2 := ihn e2 hn2 true hbound2
          step*
          · intro cl1 hcl1 cl2 hcl2
            have hb1 := cnfPure_clause_length_le e1 true cl1.val (c_post ▸ List.mem_map_of_mem hcl1)
            have hb2 := cnfPure_clause_length_le e2 true cl2.val (c1_post ▸ List.mem_map_of_mem hcl2)
            calc cl1.val.length + cl2.val.length ≤ exprSize e1 + exprSize e2 :=
                  Nat.add_le_add hb1 hb2
              _ ≤ exprSize (expr.Expr.Conj e1 e2) := by simp only [exprSize]; exact Nat.le_succ _
              _ ≤ 2 ^ exprSize (expr.Expr.Conj e1 e2) := Nat.lt_two_pow_self.le
              _ ≤ Usize.max := hbound
          · have hlen1 : c.val.length = (cnfPure e1 true).length := by
              have h := congrArg List.length c_post
              simpa [Cnf.contents_def] using h
            have hlen2 : c1.val.length = (cnfPure e2 true).length := by
              have h := congrArg List.length c1_post
              simpa [Cnf.contents_def] using h
            have heq : c.val.length * c1.val.length =
                (cnfPure (expr.Expr.Conj e1 e2) true).length := by
              rw [hlen1, hlen2, ← distributeList_length]; rfl
            rw [heq]
            exact le_trans (cnfPure_length_le _ true) hbound
          · simp_all [cnfPure]
        · have ih1 := ihn e1 hn1 false hbound1
          have ih2 := ihn e2 hn2 false hbound2
          step*
          · have hlen1 : c.val.length = (cnfPure e1 false).length := by
              have h := congrArg List.length c_post
              simpa [Cnf.contents_def] using h
            have hlen2 : c1.val.length = (cnfPure e2 false).length := by
              have h := congrArg List.length c1_post
              simpa [Cnf.contents_def] using h
            have heq : c.val.length + c1.val.length =
                (cnfPure (expr.Expr.Conj e1 e2) false).length := by
              rw [hlen1, hlen2]; simp [cnfPure]
            rw [heq]
            exact le_trans (cnfPure_length_le _ false) hbound
          · simp_all [cnfPure]
      | Disj e1 e2 =>
        unfold cnf.cnf_rec
        have hlt1 : exprSize e1 < exprSize (expr.Expr.Disj e1 e2) := by
          simp only [exprSize]; exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
        have hlt2 : exprSize e2 < exprSize (expr.Expr.Disj e1 e2) := by
          simp only [exprSize]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
        have hn1 : exprSize e1 ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le hlt1 he)
        have hn2 : exprSize e2 ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le hlt2 he)
        have hbound1 : 2 ^ exprSize e1 ≤ Usize.max :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hlt1.le) hbound
        have hbound2 : 2 ^ exprSize e2 ≤ Usize.max :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hlt2.le) hbound
        split
        · have ih1 := ihn e1 hn1 true hbound1
          have ih2 := ihn e2 hn2 true hbound2
          step*
          · have hlen1 : c.val.length = (cnfPure e1 true).length := by
              have h := congrArg List.length c_post
              simpa [Cnf.contents_def] using h
            have hlen2 : c1.val.length = (cnfPure e2 true).length := by
              have h := congrArg List.length c1_post
              simpa [Cnf.contents_def] using h
            have heq : c.val.length + c1.val.length =
                (cnfPure (expr.Expr.Disj e1 e2) true).length := by
              rw [hlen1, hlen2]; simp [cnfPure]
            rw [heq]
            exact le_trans (cnfPure_length_le _ true) hbound
          · simp_all [cnfPure]
        · have ih1 := ihn e1 hn1 false hbound1
          have ih2 := ihn e2 hn2 false hbound2
          step*
          · intro cl1 hcl1 cl2 hcl2
            have hb1 := cnfPure_clause_length_le e1 false cl1.val (c_post ▸ List.mem_map_of_mem hcl1)
            have hb2 := cnfPure_clause_length_le e2 false cl2.val (c1_post ▸ List.mem_map_of_mem hcl2)
            calc cl1.val.length + cl2.val.length ≤ exprSize e1 + exprSize e2 :=
                  Nat.add_le_add hb1 hb2
              _ ≤ exprSize (expr.Expr.Disj e1 e2) := by simp only [exprSize]; exact Nat.le_succ _
              _ ≤ 2 ^ exprSize (expr.Expr.Disj e1 e2) := Nat.lt_two_pow_self.le
              _ ≤ Usize.max := hbound
          · have hlen1 : c.val.length = (cnfPure e1 false).length := by
              have h := congrArg List.length c_post
              simpa [Cnf.contents_def] using h
            have hlen2 : c1.val.length = (cnfPure e2 false).length := by
              have h := congrArg List.length c1_post
              simpa [Cnf.contents_def] using h
            have heq : c.val.length * c1.val.length =
                (cnfPure (expr.Expr.Disj e1 e2) false).length := by
              rw [hlen1, hlen2, ← distributeList_length]; rfl
            rw [heq]
            exact le_trans (cnfPure_length_le _ false) hbound
          · simp_all [cnfPure]
      | Neg e' =>
        unfold cnf.cnf_rec
        have hlt : exprSize e' < exprSize (expr.Expr.Neg e') := by
          simp only [exprSize]; exact Nat.lt_succ_self _
        have hn' : exprSize e' ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le hlt he)
        have hbound' : 2 ^ exprSize e' ≤ Usize.max :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hlt.le) hbound
        have ih := ihn e' hn' (!negate) hbound'
        step*
        simp_all [cnfPure]
  exact main (exprSize e) e (le_refl _) negate hbound

/-- **Spec theorem for `sat_solver::cnf::to_cnf`**: matches `cnfPure _ false`. -/
@[step]
theorem cnf.to_cnf.spec (e : expr.Expr) (hbound : 2 ^ exprSize e ≤ Usize.max) :
    cnf.to_cnf e ⦃ (r : cnf.Cnf) => Cnf.contents r = cnfPure e false ⦄ := by
  unfold cnf.to_cnf
  step*

/-- **Spec theorem for `sat_solver::cnf::eval_literal`**: matches `Literal.eval`. -/
@[step]
theorem cnf.eval_literal.spec (lit : cnf.Literal) (m : expr.Map) (w : Std.U8 → Bool)
    (hrepr : Map.represents m [lit.var] w) :
    cnf.eval_literal lit m ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (Literal.eval w lit) ⦄ := by
  unfold cnf.eval_literal
  have hv : Map.lookupList m.val lit.var = some (w lit.var) := hrepr lit.var (by simp)
  step*
  · simp_all [Literal.eval]
  · simp_all [Literal.eval]

/-- **Spec theorem for `sat_solver::cnf::eval_clause`'s loop.** -/
@[step]
theorem cnf.eval_clause_loop.spec (iter : core.slice.iter.Iter cnf.Literal) (m : expr.Map)
    (w : Std.U8 → Bool) (hrepr : Map.represents m (clauseVars iter.val) w) :
    cnf.eval_clause_loop iter m ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (Clause.eval w iter.val) ⦄ := by
  unfold cnf.eval_clause_loop
  step*
  · exact w
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all [Clause.eval]
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => exact fun k hk => hrepr k (by simp_all [clauseVars])
  · simp only [r_post, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
    step*
    · exact w
    · obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es => simp_all [Clause.eval]
    · obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es =>
        have hiter1 : iter1.val = es := o_post.2
        rw [hiter1]
        exact fun k hk => hrepr k (by simp_all [clauseVars])
    · obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es => simp_all [Clause.eval]
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::cnf::eval_clause`**: matches `Clause.eval`. -/
@[step]
theorem cnf.eval_clause.spec (clause : cnf.Clause) (m : expr.Map) (w : Std.U8 → Bool)
    (hrepr : Map.represents m (clauseVars clause.val) w) :
    cnf.eval_clause clause m ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (Clause.eval w clause.val) ⦄ := by
  unfold cnf.eval_clause
  step*
  · exact w
  · simp_all
  · simp_all

/-- **Spec theorem for `sat_solver::cnf::eval_cnf`'s loop.** -/
@[step]
theorem cnf.eval_cnf_loop.spec (iter : core.slice.iter.Iter cnf.Clause) (m : expr.Map)
    (w : Std.U8 → Bool) (hrepr : Map.represents m (cnfVars (iter.val.map (·.val))) w) :
    cnf.eval_cnf_loop iter m ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (Cnf.eval w (iter.val.map (·.val))) ⦄ := by
  unfold cnf.eval_cnf_loop
  step*
  · exact w
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all [Cnf.eval]
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => exact fun k hk => hrepr k (by simp_all [cnfVars, clauseVars])
  · simp only [r_post, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
    step*
    · exact w
    · obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es =>
        have hiter1 : iter1.val = es := o_post.2
        rw [hiter1]
        exact fun k hk => hrepr k (by simp_all [cnfVars, clauseVars])
    · obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es => simp_all [Cnf.eval]
    · obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es => simp_all [Cnf.eval]
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::cnf::eval_cnf`**: matches `Cnf.eval`. -/
@[step]
theorem cnf.eval_cnf.spec (cnf1 : cnf.Cnf) (m : expr.Map) (w : Std.U8 → Bool)
    (hrepr : Map.represents m (cnfVars (Cnf.contents cnf1)) w) :
    cnf.eval_cnf cnf1 m ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (Cnf.eval w (Cnf.contents cnf1)) ⦄ := by
  unfold cnf.eval_cnf
  step*
  · exact w
  · simp_all
  · simp_all

/-- **Top-level correctness theorem**: converting `e` to CNF and evaluating it gives
    the same answer as evaluating `e` directly (this is `cnfPure`'s own correctness
    theorem, `Cnf.eval_cnfPure`, transported across the extraction layer). -/
@[step]
theorem cnf.eval_cnf_to_cnf.spec_of_represents (e : expr.Expr) (m : expr.Map) (w : Std.U8 → Bool)
    (hrepr : Map.represents m (varsOf e) w) (hbound : 2 ^ exprSize e ≤ Usize.max) :
    (do let c ← cnf.to_cnf e; cnf.eval_cnf c m) ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (evalPure w e) ⦄ := by
  step*
  · exact w
  · exact fun k hk => hrepr k (cnfVars_cnfPure_subset e false k (c_post ▸ hk))
  · rw [r_post, c_post, Cnf.eval_cnfPure]
    simp

end sat_solver
