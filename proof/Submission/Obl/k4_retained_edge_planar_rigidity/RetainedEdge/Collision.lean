-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/Collision.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.FiniteProb
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.Parallelogram
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.Cells

/-!
# The collision inequality of paper Lemma 7.5

Draw `m` independent pairs of independent edges `(eᵢ, eᵢ')` from a finite edge law `u` with
endpoints `A e ∈ E`, `B e ∈ F`, and `2m` independent coefficients from a finite law with values
`val`. Put `Z = ∑ᵢ (Cᵢ A eᵢ + Dᵢ B eᵢ)` and `Z'` the same sum over the primed edges.

* If every coefficient sum set `∑ᵢ (cᵢ E + dᵢ F)` occupies at most `M` cells, then `Z, Z'` lie in
  the same cell with probability at least `1/M` (Cauchy–Schwarz, `re:collision-lower`).
* If the difference vectors `vᵢ = A eᵢ - A eᵢ'`, `uᵢ = B eᵢ - B eᵢ'` have a pair with wedge above
  `Δ`, two flat coefficients make a collision unlikely (`re:collision-upper`); all wedges are at
  most `Δ` only if all `vᵢ` are short or the other edges lie in parallel strips determined by one
  long `vᵢ` (`re:bad-wedge`).
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

variable {𝔈 α : Type*} [Fintype 𝔈] [Fintype α] [DecidableEq 𝔈] [DecidableEq α]

/-- The endpoint sum `∑ᵢ (Cᵢ A eᵢ + Dᵢ B eᵢ)`. -/
def endSum (val : α → ℝ) (A B : 𝔈 → ℝ × ℝ) {m : ℕ} (γ : Fin m × Bool → α) (es : Fin m → 𝔈) :
    ℝ × ℝ :=
  ∑ i, (val (γ (i, true)) • A (es i) + val (γ (i, false)) • B (es i))

/-- The difference vectors `vᵢ, uᵢ` of a sample of edge pairs. -/
def diffVec (A B : 𝔈 → ℝ × ℝ) {m : ℕ} (ωE : Fin m → 𝔈 × 𝔈) : Fin m × Bool → ℝ × ℝ
  | (i, true) => A (ωE i).1 - A (ωE i).2
  | (i, false) => B (ωE i).1 - B (ωE i).2

/-- The law of an independent pair of edges. -/
def pairLaw (u : 𝔈 → ℝ) (p : 𝔈 × 𝔈) : ℝ := u p.1 * u p.2

theorem endSum_sub (val : α → ℝ) (A B : 𝔈 → ℝ × ℝ) {m : ℕ} (γ : Fin m × Bool → α)
    (ωE : Fin m → 𝔈 × 𝔈) :
    endSum val A B γ (fun i => (ωE i).1) - endSum val A B γ (fun i => (ωE i).2) =
      ∑ β, val (γ β) • diffVec A B ωE β := by
  unfold endSum
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [diffVec, smul_sub]
  abel

theorem finset_sum_mem_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ × ℝ)
    (S : ι → Finset (ℝ × ℝ)) (hf : ∀ i ∈ s, f i ∈ S i) : ∑ i ∈ s, f i ∈ ∑ i ∈ s, S i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Finset.add_mem_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem endSum_mem (val : α → ℝ) (A B : 𝔈 → ℝ × ℝ) {E F : Finset (ℝ × ℝ)}
    (hA : ∀ e, A e ∈ E) (hB : ∀ e, B e ∈ F) {m : ℕ} (γ : Fin m × Bool → α) (es : Fin m → 𝔈) :
    endSum val A B γ es ∈ ∑ i, (val (γ (i, true)) • E + val (γ (i, false)) • F) :=
  finset_sum_mem_sum _ _ _ fun i _ =>
    Finset.add_mem_add (Finset.smul_mem_smul_finset (hA _)) (Finset.smul_mem_smul_finset (hB _))

theorem pw_pairLaw (u : 𝔈 → ℝ) {m : ℕ} (ωE : Fin m → 𝔈 × 𝔈) :
    pw (pairLaw u) ωE = pw u (fun i => (ωE i).1) * pw u (fun i => (ωE i).2) := by
  unfold pw pairLaw
  rw [Finset.prod_mul_distrib]

theorem sum_pw_pairLaw (u : 𝔈 → ℝ) {m : ℕ} (G : (Fin m → 𝔈) → (Fin m → 𝔈) → ℝ) :
    ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE * G (fun i => (ωE i).1) (fun i => (ωE i).2) =
      ∑ es : Fin m → 𝔈, ∑ es' : Fin m → 𝔈, pw u es * pw u es' * G es es' := by
  rw [← Fintype.sum_prod_type (fun p : (Fin m → 𝔈) × (Fin m → 𝔈) => pw u p.1 * pw u p.2 * G p.1 p.2)]
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => 𝔈) (fun _ => 𝔈)) _ _
    (fun ωE => ?_)
  rw [pw_pairLaw]
  rfl

theorem sum_pairLaw (u : 𝔈 → ℝ) (hu : ∑ e, u e = 1) : ∑ p, pairLaw u p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [pairLaw, ← Finset.mul_sum, hu, mul_one]

/-- **Collision lower bound** (`re:collision-lower`): two independent endpoint sums with a fixed
coefficient tuple land in the same cell with probability at least `1/M`. -/
theorem collision_lower (u : 𝔈 → ℝ) (hu0 : ∀ e, 0 ≤ u e) (hu1 : ∑ e, u e = 1)
    (val : α → ℝ) (A B : 𝔈 → ℝ × ℝ) {E F : Finset (ℝ × ℝ)} (hA : ∀ e, A e ∈ E)
    (hB : ∀ e, B e ∈ F) {m : ℕ} (h M : ℝ) (hMpos : 0 < M) (γ : Fin m × Bool → α)
    (hM : ((cells h (∑ i, (val (γ (i, true)) • E + val (γ (i, false)) • F))).card : ℝ) ≤ M) :
    1 / M ≤ ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
      (if cell h (endSum val A B γ (fun i => (ωE i).1)) =
        cell h (endSum val A B γ (fun i => (ωE i).2)) then 1 else 0) := by
  classical
  set Zs := cells h (∑ i, (val (γ (i, true)) • E + val (γ (i, false)) • F)) with hZs
  set Z := endSum val A B γ with hZ
  have hmem : ∀ es, cell h (Z es) ∈ Zs := fun es => cell_mem_cells (endSum_mem val A B hA hB γ es)
  let p : ℤ × ℤ → ℝ := fun z => ∑ es : Fin m → 𝔈, pw u es * (if cell h (Z es) = z then 1 else 0)
  have hpsum : ∑ z ∈ Zs, p z = 1 := by
    simp only [p]
    rw [Finset.sum_comm]
    have : ∀ es : Fin m → 𝔈, ∑ z ∈ Zs, pw u es * (if cell h (Z es) = z then (1 : ℝ) else 0) =
        pw u es := by
      intro es
      rw [← Finset.mul_sum, Finset.sum_ite_eq Zs (cell h (Z es)) (fun _ => (1 : ℝ)),
        ite_eq_left (hmem es), mul_one]
    rw [Finset.sum_congr rfl fun es _ => this es]
    exact sum_pw u hu1
  have hind : ∀ es es' : Fin m → 𝔈, (if cell h (Z es) = cell h (Z es') then (1 : ℝ) else 0) =
      ∑ z ∈ Zs, (if cell h (Z es) = z then 1 else 0) * (if cell h (Z es') = z then 1 else 0) := by
    intro es es'
    by_cases heq : cell h (Z es) = cell h (Z es')
    · rw [ite_eq_left heq]
      rw [Finset.sum_eq_single (cell h (Z es))]
      · rw [ite_eq_left rfl, ← heq, ite_eq_left rfl, mul_one]
      · intro z _ hz
        rw [ite_eq_right (Ne.symm hz), zero_mul]
      · intro hn; exact absurd (hmem es) hn
    · rw [ite_eq_right heq]
      symm
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases h1 : cell h (Z es) = z
      · rw [ite_eq_left h1, ite_eq_right (fun h2 => heq (h1.trans h2.symm)), mul_zero]
      · rw [ite_eq_right h1, zero_mul]
  have hcoll : ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
      (if cell h (Z (fun i => (ωE i).1)) = cell h (Z (fun i => (ωE i).2)) then 1 else 0) =
      ∑ z ∈ Zs, p z ^ 2 := by
    calc ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
          (if cell h (Z (fun i => (ωE i).1)) = cell h (Z (fun i => (ωE i).2)) then (1 : ℝ) else 0)
        = ∑ es : Fin m → 𝔈, ∑ es' : Fin m → 𝔈, pw u es * pw u es' *
            (if cell h (Z es) = cell h (Z es') then (1 : ℝ) else 0) :=
          sum_pw_pairLaw u (fun es es' => if cell h (Z es) = cell h (Z es') then (1 : ℝ) else 0)
      _ = ∑ es : Fin m → 𝔈, ∑ es' : Fin m → 𝔈, ∑ z ∈ Zs,
            (pw u es * (if cell h (Z es) = z then (1 : ℝ) else 0)) *
              (pw u es' * (if cell h (Z es') = z then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun es _ => Finset.sum_congr rfl fun es' _ => ?_
          rw [hind, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          ring
      _ = ∑ es : Fin m → 𝔈, ∑ z ∈ Zs, ∑ es' : Fin m → 𝔈,
            (pw u es * (if cell h (Z es) = z then (1 : ℝ) else 0)) *
              (pw u es' * (if cell h (Z es') = z then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl fun es _ => Finset.sum_comm
      _ = ∑ z ∈ Zs, ∑ es : Fin m → 𝔈, ∑ es' : Fin m → 𝔈,
            (pw u es * (if cell h (Z es) = z then (1 : ℝ) else 0)) *
              (pw u es' * (if cell h (Z es') = z then (1 : ℝ) else 0)) := Finset.sum_comm
      _ = ∑ z ∈ Zs, p z ^ 2 := by
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [p]
          rw [sq, Finset.sum_mul_sum]
  rw [hcoll]
  have hCS := sq_sum_le_card_mul_sum_sq (s := Zs) (f := p)
  rw [hpsum, one_pow] at hCS
  have hZsM : (Zs.card : ℝ) ≤ M := hM
  have hpos : 0 ≤ ∑ z ∈ Zs, p z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  rw [div_le_iff₀ hMpos]
  calc (1 : ℝ) ≤ Zs.card * ∑ z ∈ Zs, p z ^ 2 := hCS
    _ ≤ M * ∑ z ∈ Zs, p z ^ 2 := by gcongr
    _ = (∑ z ∈ Zs, p z ^ 2) * M := by ring


theorem box_of_cell_eq {h : ℝ} (hh : 0 < h) {Z Z' : ℝ × ℝ} (hc : cell h Z = cell h Z') :
    |(Z - Z').1| ≤ h ∧ |(Z - Z').2| ≤ h := by
  simp only [cell, Prod.mk.injEq] at hc
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hc.1
  have h2 := Int.abs_sub_lt_one_of_floor_eq_floor hc.2
  rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at h1 h2
  exact ⟨h1.le, h2.le⟩

theorem sum_update_two {ι : Type*} [Fintype ι] [DecidableEq ι] (val : α → ℝ) {β₁ β₂ : ι}
    (hne : β₁ ≠ β₂) (γ : ι → α) (x y : α) (V : ι → ℝ × ℝ) :
    ∑ β, val (Function.update (Function.update γ β₂ y) β₁ x β) • V β =
      val x • V β₁ + val y • V β₂ + ∑ β, (if β = β₁ ∨ β = β₂ then 0 else val (γ β) • V β) := by
  have hpt : ∀ β, val (Function.update (Function.update γ β₂ y) β₁ x β) • V β =
      (if β = β₁ then val x • V β₁ else 0) + (if β = β₂ then val y • V β₂ else 0) +
        (if β = β₁ ∨ β = β₂ then 0 else val (γ β) • V β) := by
    intro β
    by_cases h1 : β = β₁
    · subst h1
      simp [hne]
    · by_cases h2 : β = β₂
      · subst h2
        simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun β _ => hpt β, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

/-- **Collision upper bound for a transverse sample** (`re:collision-upper`). -/
theorem good_upper (w : α → ℝ) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (val : α → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h φ Δ D : ℝ} (hh : 0 < h) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1) (hflat : ∀ x, lawMass w val (Set.Icc (x - h) (x + h)) ≤ φ)
    (V : ι → ℝ × ℝ) (hgood : ∃ β₁ β₂, Δ < |wedge (V β₁) (V β₂)|)
    (hVD : ∀ β, max |(V β).1| |(V β).2| ≤ 2 * D) :
    ∑ γ : ι → α, pw w γ * (if |(∑ β, val (γ β) • V β).1| ≤ h ∧
      |(∑ β, val (γ β) • V β).2| ≤ h then 1 else 0) ≤ (10 + 8 * D) / Δ * φ ^ 2 := by
  classical
  -- order the transverse pair so that the second vector is the larger one
  obtain ⟨β₁, β₂, hβ, hle⟩ : ∃ β₁ β₂, Δ < |wedge (V β₁) (V β₂)| ∧
      max |(V β₁).1| |(V β₁).2| ≤ max |(V β₂).1| |(V β₂).2| := by
    obtain ⟨b₁, b₂, hb⟩ := hgood
    rcases le_total (max |(V b₁).1| |(V b₁).2|) (max |(V b₂).1| |(V b₂).2|) with hc | hc
    · exact ⟨b₁, b₂, hb, hc⟩
    · refine ⟨b₂, b₁, ?_, hc⟩
      rwa [wedge_comm, abs_neg]
  have hne : β₁ ≠ β₂ := by
    intro heq; rw [heq, wedge_self, abs_zero] at hβ; linarith
  set g : (ι → α) → ℝ := fun γ => if |(∑ β, val (γ β) • V β).1| ≤ h ∧
      |(∑ β, val (γ β) • V β).2| ≤ h then 1 else 0 with hg
  have hres := sum_resample w hw1 β₁ g
  have hres2 := sum_resample w hw1 β₂ (fun γ => ∑ x, w x * g (Function.update γ β₁ x))
  rw [hres, hres2]
  have hφ : 0 ≤ φ := le_trans (lawMass_nonneg hw0 val _) (hflat 0)
  have hpt : ∀ γ : ι → α, ∑ y, w y * ∑ x, w x * g (Function.update (Function.update γ β₂ y) β₁ x)
      ≤ (10 + 8 * D) / Δ * φ ^ 2 := by
    intro γ
    have hpair := pair_collision_le hw0 val hh hΔ hΔ1 hflat (V β₁) (V β₂)
      (∑ β, (if β = β₁ ∨ β = β₂ then 0 else val (γ β) • V β)) hβ.le hle (hVD β₂)
    calc ∑ y, w y * ∑ x, w x * g (Function.update (Function.update γ β₂ y) β₁ x)
        = ∑ x, ∑ y, w x * w y * (if |(val x • V β₁ + val y • V β₂ +
            ∑ β, (if β = β₁ ∨ β = β₂ then 0 else val (γ β) • V β)).1| ≤ h ∧
            |(val x • V β₁ + val y • V β₂ +
            ∑ β, (if β = β₁ ∨ β = β₂ then 0 else val (γ β) • V β)).2| ≤ h then 1 else 0) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [hg, sum_update_two val hne γ x y V]
          ring
      _ ≤ (10 + 8 * D) / Δ * φ ^ 2 := hpair
  calc ∑ γ : ι → α, pw w γ * ∑ y, w y * ∑ x, w x * g (Function.update (Function.update γ β₂ y) β₁ x)
      ≤ ∑ γ : ι → α, pw w γ * ((10 + 8 * D) / Δ * φ ^ 2) :=
        Finset.sum_le_sum fun γ _ => mul_le_mul_of_nonneg_left (hpt γ) (pw_nonneg hw0 γ)
    _ = (10 + 8 * D) / Δ * φ ^ 2 := by rw [← Finset.sum_mul, sum_pw w hw1, one_mul]


/-- A pair of edges whose first endpoints are close. -/
abbrev shortPair (A : 𝔈 → ℝ × ℝ) (q : ℝ) (p : 𝔈 × 𝔈) : Prop :=
  max |(A p.1 - A p.2).1| |(A p.1 - A p.2).2| < q

/-- The pair `p'` lies in the parallel strips determined by a long difference `v` of `p`. -/
abbrev stripPair (A B : 𝔈 → ℝ × ℝ) (q Δ : ℝ) (p p' : 𝔈 × 𝔈) : Prop :=
  q ≤ max |(A p.1 - A p.2).1| |(A p.1 - A p.2).2| ∧
    |wedge (A p'.1 - A p'.2) (A p.1 - A p.2)| ≤ Δ ∧ |wedge (B p'.1 - B p'.2) (A p.1 - A p.2)| ≤ Δ

theorem pairLaw_nonneg {u : 𝔈 → ℝ} (hu0 : ∀ e, 0 ≤ u e) (p : 𝔈 × 𝔈) : 0 ≤ pairLaw u p :=
  mul_nonneg (hu0 _) (hu0 _)

/-- **The bad-wedge event** (`re:bad-wedge`): all wedges of the difference vectors are small only
if all first differences are short, or all other edges lie in strips set by one long difference. -/
theorem bad_upper (u : 𝔈 → ℝ) (hu0 : ∀ e, 0 ≤ u e) (hu1 : ∑ e, u e = 1) (A B : 𝔈 → ℝ × ℝ)
    {m : ℕ} {q Δ θ π : ℝ} (hπ0 : 0 ≤ π)
    (hθ : ∑ p, pairLaw u p * (if shortPair A q p then 1 else 0) ≤ θ)
    (hπ : ∀ v : ℝ × ℝ, q ≤ max |v.1| |v.2| → ∀ x₀ y₀ : ℝ × ℝ,
      ∑ e, u e * (if |wedge (A e - x₀) v| ≤ Δ ∧ |wedge (B e - y₀) v| ≤ Δ then 1 else 0) ≤ π) :
    ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
      (if ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ then 1 else 0) ≤
      θ ^ m + m * π ^ (m - 1) := by
  classical
  have hpl0 := pairLaw_nonneg hu0
  have hpl1 := sum_pairLaw u hu1
  have hpt : ∀ ωE : Fin m → 𝔈 × 𝔈,
      (if ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ then (1 : ℝ) else 0) ≤
        (if ∀ j, shortPair A q (ωE j) then 1 else 0) +
          ∑ i, (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then 1 else 0) := by
    intro ωE
    have hnn : 0 ≤ ∑ i, (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    by_cases hb : ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ
    · rw [ite_eq_left hb]
      by_cases hs : ∀ j, shortPair A q (ωE j)
      · rw [ite_eq_left hs]; linarith
      · rw [ite_eq_right hs, zero_add]
        push Not at hs
        obtain ⟨i, hi⟩ := hs
        have hi' : q ≤ max |(A (ωE i).1 - A (ωE i).2).1| |(A (ωE i).1 - A (ωE i).2).2| := hi
        have hterm : (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then (1 : ℝ) else 0) = 1 := by
          rw [ite_eq_left]
          intro j _
          exact ⟨hi', hb (j, true) (i, true), hb (j, false) (i, true)⟩
        calc (1 : ℝ) = (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then (1 : ℝ) else 0) :=
              hterm.symm
          _ ≤ ∑ i, (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then (1 : ℝ) else 0) :=
              Finset.single_le_sum (f := fun i => if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j)
                then (1 : ℝ) else 0) (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · rw [ite_eq_right hb]
      exact add_nonneg (by split_ifs <;> norm_num) hnn
  have hfirst : ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
      (if ∀ j, shortPair A q (ωE j) then 1 else 0) ≤ θ ^ m := by
    have h1 := sum_pw_forall (ι := Fin m) (pairLaw u) (fun _ p => shortPair A q p)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    rw [show (∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
        (if ∀ j, shortPair A q (ωE j) then (1 : ℝ) else 0)) =
        (∑ p, pairLaw u p * (if shortPair A q p then 1 else 0)) ^ m by convert h1]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ =>
      mul_nonneg (hpl0 p) (by split_ifs <;> norm_num)) hθ m
  have hT : ∀ p : 𝔈 × 𝔈, ∑ p', pairLaw u p' * (if stripPair A B q Δ p p' then 1 else 0) ≤ π := by
    intro p
    by_cases hq : q ≤ max |(A p.1 - A p.2).1| |(A p.1 - A p.2).2|
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      calc ∑ e', ∑ e, pairLaw u (e, e') * (if stripPair A B q Δ p (e, e') then (1 : ℝ) else 0)
          = ∑ e', u e' * ∑ e, u e * (if |wedge (A e - A e') (A p.1 - A p.2)| ≤ Δ ∧
              |wedge (B e - B e') (A p.1 - A p.2)| ≤ Δ then 1 else 0) := by
            refine Finset.sum_congr rfl fun e' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            simp only [pairLaw, stripPair, hq, true_and]
            ring
        _ ≤ ∑ e', u e' * π := Finset.sum_le_sum fun e' _ =>
            mul_le_mul_of_nonneg_left (hπ _ hq (A e') (B e')) (hu0 e')
        _ = π := by rw [← Finset.sum_mul, hu1, one_mul]
    · have : ∀ p', (if stripPair A B q Δ p p' then (1 : ℝ) else 0) = 0 := fun p' =>
        ite_eq_right fun hs => hq hs.1
      simp only [this, mul_zero, Finset.sum_const_zero]
      exact hπ0
  have hsecond : ∀ i : Fin m, ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
      (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then 1 else 0) ≤ π ^ (m - 1) := by
    intro i
    have := sum_pw_forall_ne_le (pairLaw u) hpl0 hpl1 i (stripPair A B q Δ) π hT
    rw [Fintype.card_fin] at this
    convert this
  calc ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
        (if ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ then 1 else 0)
      ≤ ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
          ((if ∀ j, shortPair A q (ωE j) then 1 else 0) +
            ∑ i, (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then 1 else 0)) :=
        Finset.sum_le_sum fun ωE _ => mul_le_mul_of_nonneg_left (hpt ωE) (pw_nonneg hpl0 ωE)
    _ = ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE * (if ∀ j, shortPair A q (ωE j) then 1 else 0) +
          ∑ i, ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
            (if ∀ j, j ≠ i → stripPair A B q Δ (ωE i) (ωE j) then 1 else 0) := by
        rw [← Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ωE _ => ?_
        rw [mul_add, Finset.mul_sum]
    _ ≤ θ ^ m + ∑ _i : Fin m, π ^ (m - 1) := add_le_add hfirst (Finset.sum_le_sum fun i _ => hsecond i)
    _ = θ ^ m + m * π ^ (m - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem diffVec_le (A B : 𝔈 → ℝ × ℝ) {D : ℝ} (hAD : ∀ e, max |(A e).1| |(A e).2| ≤ D)
    (hBD : ∀ e, max |(B e).1| |(B e).2| ≤ D) {m : ℕ} (ωE : Fin m → 𝔈 × 𝔈) (β : Fin m × Bool) :
    max |(diffVec A B ωE β).1| |(diffVec A B ωE β).2| ≤ 2 * D := by
  have key : ∀ x y : ℝ × ℝ, max |x.1| |x.2| ≤ D → max |y.1| |y.2| ≤ D →
      max |(x - y).1| |(x - y).2| ≤ 2 * D := by
    intro x y hx hy
    simp only [Prod.fst_sub, Prod.snd_sub]
    have hx1 := le_trans (le_max_left _ _) hx
    have hx2 := le_trans (le_max_right _ _) hx
    have hy1 := le_trans (le_max_left _ _) hy
    have hy2 := le_trans (le_max_right _ _) hy
    refine max_le ?_ ?_
    · exact (abs_sub _ _).trans (by linarith)
    · exact (abs_sub _ _).trans (by linarith)
  obtain ⟨i, b⟩ := β
  cases b
  · exact key _ _ (hBD _) (hBD _)
  · exact key _ _ (hAD _) (hAD _)

/-- **The collision inequality of paper Lemma 7.5**: the lower bound `1/M` for a collision of the
two endpoint sums is at most the bad-wedge probability plus the transverse collision bound. -/
theorem collision_inequality (u : 𝔈 → ℝ) (hu0 : ∀ e, 0 ≤ u e) (hu1 : ∑ e, u e = 1)
    (w : α → ℝ) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (val : α → ℝ)
    (A B : 𝔈 → ℝ × ℝ) {E F : Finset (ℝ × ℝ)} (hA : ∀ e, A e ∈ E) (hB : ∀ e, B e ∈ F) {m : ℕ}
    {h φ Δ D q θ π M : ℝ} (hh : 0 < h) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hπ0 : 0 ≤ π) (hMpos : 0 < M)
    (hflat : ∀ x, lawMass w val (Set.Icc (x - h) (x + h)) ≤ φ)
    (hAD : ∀ e, max |(A e).1| |(A e).2| ≤ D) (hBD : ∀ e, max |(B e).1| |(B e).2| ≤ D)
    (hM : ∀ γ : Fin m × Bool → α,
      ((cells h (∑ i, (val (γ (i, true)) • E + val (γ (i, false)) • F))).card : ℝ) ≤ M)
    (hθ : ∑ p, pairLaw u p * (if shortPair A q p then 1 else 0) ≤ θ)
    (hπ : ∀ v : ℝ × ℝ, q ≤ max |v.1| |v.2| → ∀ x₀ y₀ : ℝ × ℝ,
      ∑ e, u e * (if |wedge (A e - x₀) v| ≤ Δ ∧ |wedge (B e - y₀) v| ≤ Δ then 1 else 0) ≤ π) :
    1 / M ≤ θ ^ m + m * π ^ (m - 1) + (10 + 8 * D) / Δ * φ ^ 2 := by
  classical
  have hpl0 := pairLaw_nonneg hu0
  have hpl1 := sum_pairLaw u hu1
  have hD : 0 ≤ D := by
    obtain ⟨e⟩ : Nonempty 𝔈 := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      simp at hu1
    exact le_trans (le_max_of_le_left (abs_nonneg _)) (hAD e)
  have hC : 0 ≤ (10 + 8 * D) / Δ * φ ^ 2 := by positivity
  set coll : (Fin m → 𝔈 × 𝔈) → (Fin m × Bool → α) → ℝ := fun ωE γ =>
    if cell h (endSum val A B γ (fun i => (ωE i).1)) =
      cell h (endSum val A B γ (fun i => (ωE i).2)) then 1 else 0 with hcoll
  have hcoll0 : ∀ ωE γ, 0 ≤ coll ωE γ := fun ωE γ => by simp only [hcoll]; split_ifs <;> norm_num
  -- the lower bound, conditioning on the coefficients
  have hlow : 1 / M ≤ ∑ γ : Fin m × Bool → α, pw w γ * ∑ ωE : Fin m → 𝔈 × 𝔈,
      pw (pairLaw u) ωE * coll ωE γ := by
    calc 1 / M = ∑ γ : Fin m × Bool → α, pw w γ * (1 / M) := by
          rw [← Finset.sum_mul, sum_pw w hw1, one_mul]
      _ ≤ ∑ γ : Fin m × Bool → α, pw w γ * ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE * coll ωE γ :=
          Finset.sum_le_sum fun γ _ => mul_le_mul_of_nonneg_left
            (collision_lower u hu0 hu1 val A B hA hB h M hMpos γ (hM γ)) (pw_nonneg hw0 γ)
  -- the upper bound, conditioning on the edges
  have hup : ∀ ωE : Fin m → 𝔈 × 𝔈, ∑ γ : Fin m × Bool → α, pw w γ * coll ωE γ ≤
      (if ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ then 1 else 0) +
        (10 + 8 * D) / Δ * φ ^ 2 := by
    intro ωE
    by_cases hb : ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ
    · rw [ite_eq_left hb]
      calc ∑ γ : Fin m × Bool → α, pw w γ * coll ωE γ ≤ ∑ γ : Fin m × Bool → α, pw w γ * 1 :=
            Finset.sum_le_sum fun γ _ => mul_le_mul_of_nonneg_left
              (by simp only [hcoll]; split_ifs <;> norm_num) (pw_nonneg hw0 γ)
        _ = 1 := by rw [← Finset.sum_mul, sum_pw w hw1, one_mul]
        _ ≤ 1 + (10 + 8 * D) / Δ * φ ^ 2 := le_add_of_nonneg_right hC
    · rw [ite_eq_right hb, zero_add]
      push Not at hb
      obtain ⟨β, β', hbb⟩ := hb
      calc ∑ γ : Fin m × Bool → α, pw w γ * coll ωE γ
          ≤ ∑ γ : Fin m × Bool → α, pw w γ *
              (if |(∑ β, val (γ β) • diffVec A B ωE β).1| ≤ h ∧
                |(∑ β, val (γ β) • diffVec A B ωE β).2| ≤ h then 1 else 0) := by
            refine Finset.sum_le_sum fun γ _ => mul_le_mul_of_nonneg_left ?_ (pw_nonneg hw0 γ)
            simp only [hcoll]
            split_ifs with h1 h2
            · exact le_refl _
            · exfalso; apply h2
              rw [← endSum_sub]
              exact box_of_cell_eq hh h1
            · norm_num
            · exact le_refl _
        _ ≤ (10 + 8 * D) / Δ * φ ^ 2 :=
            good_upper w hw0 hw1 val hh hΔ hΔ1 hflat (diffVec A B ωE) ⟨β, β', hbb⟩
              (diffVec_le A B hAD hBD ωE)
  have hswap : ∑ γ : Fin m × Bool → α, pw w γ * ∑ ωE : Fin m → 𝔈 × 𝔈,
      pw (pairLaw u) ωE * coll ωE γ = ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
        ∑ γ : Fin m × Bool → α, pw w γ * coll ωE γ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ωE _ => Finset.sum_congr rfl fun γ _ => ?_
    ring
  calc 1 / M ≤ ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
        ∑ γ : Fin m × Bool → α, pw w γ * coll ωE γ := hswap ▸ hlow
    _ ≤ ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
          ((if ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ then 1 else 0) +
            (10 + 8 * D) / Δ * φ ^ 2) :=
        Finset.sum_le_sum fun ωE _ => mul_le_mul_of_nonneg_left (hup ωE) (pw_nonneg hpl0 ωE)
    _ = ∑ ωE : Fin m → 𝔈 × 𝔈, pw (pairLaw u) ωE *
          (if ∀ β β', |wedge (diffVec A B ωE β) (diffVec A B ωE β')| ≤ Δ then 1 else 0) +
            (10 + 8 * D) / Δ * φ ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, sum_pw (pairLaw u) hpl1, one_mul]
    _ ≤ θ ^ m + m * π ^ (m - 1) + (10 + 8 * D) / Δ * φ ^ 2 := by
        gcongr
        exact bad_upper u hu0 hu1 A B hπ0 hθ hπ

end

end Submission.Obl.k4_retained_edge_planar_rigidity
