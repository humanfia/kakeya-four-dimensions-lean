-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Assembly.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Assembly.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Family
import Submission.Obl.k4_clean_cover_graph_atlas.Frames
import Submission.Obl.k4_clean_cover_graph_atlas.ChartTests
import Submission.Obl.k4_clean_cover_graph_atlas.SliceFormats

/-!
# From a label system to the preliminary improved atlas

A *label system* at a sample consists of finitely many labels, each with an old path chart
(packet) at one level `i`, a sub-block `jj < 2^{s₀}` of its block, a box `bx` of side
`2^{-s₀}` in its normalized coordinates, a representative quadratic test `Rep` with a
normalization `lam` and curvature type `low`, a branch `fbr` (a function of the base point),
a geometric member set `mem` (Boolean format, contained in the packet's lines whose midpoint
position lies in the box), and a set `good ⊆ mem` of lines that stay within `ηt / B` of the
normalized branch on the whole sub-block; and a list rule at the terminal observation whose
success on good incidences carries mass `≥ N^{-ζ}`.

`preImprovementAt_of_labels` builds the charts: the frame is the scaled old frame
(`Frames.gchart_subbox`), the test is `labelTest`, the lines are `mem ∩ testSet`, the incidences
are cut by the derivative lower bound, and the depth `r₂` has `27 ηt ≤ N^ζ δ(r₂) ≤ 4 N^{2ζ} ηt`.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The sub-block of a label. -/
def subBlock (T s₀ j₀ jj : ℕ) : Set ℝ :=
  Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
    (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))

theorem subBlock_lt (T s₀ j₀ jj : ℕ) :
    (subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀) < ((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀) :=
  div_lt_div_of_pos_right (by linarith) (by positivity)

theorem mid_mem_subBlock (T s₀ j₀ jj : ℕ) :
    ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀) +
      ((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀)) / 2 ∈ subBlock T s₀ j₀ jj := by
  have h := subBlock_lt T s₀ j₀ jj
  constructor <;> linarith

/-- The label system data, with the improved chart of each label. -/
theorem preImprovementAt_of_labels
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {κ₁ Δ : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {Mi Di : ℕ} {ζ : ℝ}
    {C : ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {ex : Fin C → Prop} {κ : ℝ} {Mp Dp : ℕ} {i : ℕ} {rold : ℝ}
    -- the label system
    {ι : Type} [Fintype ι] (pk : ι → Fin C) (jj : ι → ℕ) (bx : ι → Fin 2 → ℤ)
    (Rep : ι → MvPolynomial (Fin 4) ℝ) (low : ι → Bool) (lam : ι → ℝ)
    (fbr : ι → (Fin 3 → ℝ) → ℝ) (mem good : ι → Set (ℕ × (Fin 6 → ℝ)))
    (lst' : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset ι) (s₀ : ℕ) (ηt r₂ : ℝ)
    {ME DE Mmem Dmem : ℕ}
    -- the sample
    (hNk : 1 ≤ Nk) (hB : ∀ w, 0 < B w)
    (hE : ∀ w q, gfmt 7 (Nk ^ ME) DE {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E w})
    -- the old charts
    (hold : ∀ ℓ, gchart Nk Mp Dp κ (T i) (j (pk ℓ) : ℝ) rold (B (γ (pk ℓ))) (E (γ (pk ℓ)))
      (c (pk ℓ)) (u (pk ℓ)) (Q (pk ℓ)) (R (pk ℓ)) (A (pk ℓ)) (F (pk ℓ)) (ex (pk ℓ)))
    (hjlt : ∀ ℓ, j (pk ℓ) < 2 ^ T i)
    -- labels
    (hjj : ∀ ℓ, jj ℓ < 2 ^ s₀)
    (hRep : ∀ ℓ, (Rep ℓ).totalDegree ≤ 2)
    (hlam : ∀ ℓ, 0 < lam ℓ) (hηt : 0 < ηt)
    (hlow : ∀ ℓ, low ℓ = true → |qc (Rep ℓ)| * (ηt / B (γ (pk ℓ))) ≤ (lam ℓ)⁻¹ / 4)
    (hhigh : ∀ ℓ, low ℓ = false → (lam ℓ)⁻¹ / 4 < |qc (Rep ℓ)| * (ηt / B (γ (pk ℓ))))
    (hcoef : ∀ ℓ e, |(labelTest (low ℓ) (B (γ (pk ℓ))) (lam ℓ) (Rep ℓ)).coeff e| ≤ Nk ^ Mi)
    (hmemA : ∀ ℓ, ∀ l ∈ mem ℓ, l ∈ A (pk ℓ) ∧
      inBox s₀ (bx ℓ) (zc (Q (pk ℓ)) (c (pk ℓ)) (u (pk ℓ)) l (subMid (T i) s₀ (j (pk ℓ)) (jj ℓ))))
    (hmemfmt : ∀ ℓ q, gfmt 6 (Nk ^ Mmem) Dmem {z | (q, z) ∈ mem ℓ})
    (hne : ∀ ℓ, (mem ℓ).Nonempty)
    (hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → γ (pk ℓ) = γ (pk ℓ') →
      subIdx s₀ (j (pk ℓ)) (jj ℓ) = subIdx s₀ (j (pk ℓ')) (jj ℓ') → Disjoint (mem ℓ) (mem ℓ'))
    (hgood : ∀ ℓ, ∀ l ∈ good ℓ, l ∈ mem ℓ ∧ ∀ t ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ),
      eval (Fin.snoc (Fin.init (gx l t)) (fbr ℓ (Fin.init (gx l t))) : Fin 4 → ℝ) (Rep ℓ) = 0 ∧
      1 / 2 ≤ lam ℓ * |eval (Fin.snoc (Fin.init (gx l t)) (fbr ℓ (Fin.init (gx l t))) : Fin 4 → ℝ)
        (pderiv 3 (Rep ℓ))| ∧
      lam ℓ * |eval (Fin.snoc (Fin.init (gx l t)) (fbr ℓ (Fin.init (gx l t))) : Fin 4 → ℝ)
        (pderiv 3 (Rep ℓ))| ≤ 2 ∧
      |gx l t 3 - fbr ℓ (Fin.init (gx l t))| ≤ ηt / B (γ (pk ℓ)))
    -- lists and success
    (hlst : ∀ w o, ((lst' w o).card : ℝ) ≤ Nk ^ ζ)
    (hlstm : ∀ w ℓ, MeasurableSet {o | ℓ ∈ lst' w o})
    (hsucc : ENNReal.ofReal (Nk ^ (-ζ)) ≤ ∑ ℓ, ENNReal.ofReal (ω (γ (pk ℓ))) *
      ((ν (γ (pk ℓ))).prod volume) {p | p ∈ E (γ (pk ℓ)) ∧ p.1 ∈ good ℓ ∧
        p.2 ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ) ∧
        ℓ ∈ lst' (γ (pk ℓ)) (obs (B (γ (pk ℓ))) (δ Nk L) p)})
    -- parameters
    (hκ : κ + 1 ≤ Nk ^ ζ) (h9 : 9 ≤ Nk ^ ζ)
    (hδlo : 27 * ηt ≤ Nk ^ ζ * gδ Nk r₂) (hδhi : gδ Nk r₂ ≤ 4 * Nk ^ ζ * ηt)
    (hMi : Mp ≤ Mi) (hcu : Nk ^ Mp + κ * (κ + 1) ≤ Nk ^ Mi)
    (hfr : (side s₀)⁻¹ * Nk ^ Mp ≤ Nk ^ Mi)
    (hfmtMi : Nk ^ ME + Nk ^ Mmem + 8 ≤ Nk ^ Mi) (hDi : max DE (max Dmem 4) ≤ Di)
    (hcard : (Fintype.card ι : ℝ) ≤ Nk ^ Mi)
    (hdepth : r₂ + Δ * L ≤ L)
    (himp : (Δ * L ≤ r₂ ∧ (2 : ℝ) ^ (T i + s₀) ≤ Nk ^ (κ₁ * Δ * L / 2)) ∨
      ∃ i', i' < m ∧ r i' + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ (T i + s₀) ≤ (2 : ℝ) ^ T i' * Nk ^ (κ₁ * Δ * L / 2)) :
    preImprovementAt Nk L W ω ν E B κ₁ Δ m r T nw Mi Di ζ := by
  classical
  set κ' := Nk ^ ζ with hκ'
  -- the chart data
  let R₂ : ι → MvPolynomial (Fin 4) ℝ := fun ℓ => labelTest (low ℓ) (B (γ (pk ℓ))) (lam ℓ) (Rep ℓ)
  let ta : ι → ℝ := fun ℓ => (subIdx s₀ (j (pk ℓ)) (jj ℓ) : ℝ) / (2 : ℝ) ^ (T i + s₀)
  let tb : ι → ℝ := fun ℓ => ((subIdx s₀ (j (pk ℓ)) (jj ℓ) : ℝ) + 1) / (2 : ℝ) ^ (T i + s₀)
  let A₂ : ι → Set (ℕ × (Fin 6 → ℝ)) := fun ℓ =>
    mem ℓ ∩ testSet (R₂ ℓ) (ta ℓ) (tb ℓ) (9 * ηt) (9 * B (γ (pk ℓ)) / 4)
  let F₂ : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun ℓ =>
    {p | p ∈ E (γ (pk ℓ)) ∧ p.1 ∈ A₂ ℓ ∧ p.2 ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ) ∧
      B (γ (pk ℓ)) / κ' ≤ |eval (gx p.1 p.2) (pderiv 3 (R₂ ℓ))|}
  have hR₂deg : ∀ ℓ, (R₂ ℓ).totalDegree ≤ 2 := fun ℓ => totalDegree_labelTest_le (hRep ℓ)
  have hκ'pos : 0 < κ' := lt_of_lt_of_le (by norm_num) h9
  -- good lines lie in the three-point sets and give the derivative lower bound
  have hgoodA : ∀ ℓ, ∀ l ∈ good ℓ, l ∈ A₂ ℓ ∧ ∀ t ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ),
      B (γ (pk ℓ)) / 4 ≤ |eval (gx l t) (pderiv 3 (R₂ ℓ))| := by
    intro ℓ l hl
    obtain ⟨hlm, hcl⟩ := hgood ℓ l hl
    have hb : ∀ t ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ),
        |eval (gx l t) (R₂ ℓ)| ≤ 9 * ηt ∧ B (γ (pk ℓ)) / 4 ≤ |eval (gx l t) (pderiv 3 (R₂ ℓ))| ∧
        |eval (gx l t) (pderiv 3 (R₂ ℓ))| ≤ 9 * B (γ (pk ℓ)) / 4 := by
      intro t ht
      obtain ⟨h1, h2, h3, h4⟩ := hcl t ht
      have := labelTest_bounds (hRep ℓ) (hlam ℓ) hηt (hB _) (hlow ℓ) (hhigh ℓ) h1 h2 h3 h4
      exact ⟨this.1, this.2.1, this.2.2.1⟩
    have hta : ta ℓ ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ) :=
      ⟨le_rfl, (subBlock_lt _ _ _ _).le⟩
    have htb : tb ℓ ∈ subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ) :=
      ⟨(subBlock_lt _ _ _ _).le, le_rfl⟩
    have htm := mid_mem_subBlock (T i) s₀ (j (pk ℓ)) (jj ℓ)
    refine ⟨⟨hlm, (hb _ hta).1, (hb _ htm).1, (hb _ htb).1, (hb _ hta).2.2, (hb _ htb).2.2⟩,
      fun t ht => (hb t ht).2.1⟩
  -- the charts
  let j₂ : ι → Fin (2 ^ (T i + s₀)) := fun ℓ =>
    ⟨subIdx s₀ (j (pk ℓ)) (jj ℓ), subIdx_lt (hjlt ℓ) (hjj ℓ)⟩
  have hchart : ∀ ℓ, chart Nk Mi Di κ' (T i + s₀) ((j₂ ℓ : ℕ) : ℝ) r₂ (B (γ (pk ℓ)))
      (E (γ (pk ℓ))) (c (pk ℓ) + Matrix.toEuclideanLin (Q (pk ℓ)) (boxCenter s₀ (bx ℓ)))
      (u (pk ℓ)) (subFrame (Q (pk ℓ)) s₀) (R₂ ℓ) (A₂ ℓ) (F₂ ℓ) True := by
    intro ℓ
    have hBℓ := hB (γ (pk ℓ))
    have hO := hold ℓ
    -- frame bounds
    have hcuℓ : ‖c (pk ℓ) + Matrix.toEuclideanLin (Q (pk ℓ)) (boxCenter s₀ (bx ℓ))‖ +
        ‖u (pk ℓ)‖ ≤ Nk ^ Mi := by
      obtain ⟨l, hl⟩ := hne ℓ
      obtain ⟨hlA, hbox⟩ := hmemA ℓ l hl
      exact (subCenter_norm_le hO (hjj ℓ) hlA hbox).trans hcu
    have hfrℓ := (subFrame_complexity_le hO.1 s₀ hO.2.2.1).trans
      ((mul_le_mul_of_nonneg_left le_rfl (inv_nonneg.mpr (side_pos s₀).le)).trans hfr)
    -- formats
    have hfA : ∀ q, gfmt 6 (Nk ^ Mmem + 5) (max Dmem 4) {z | (q, z) ∈ A₂ ℓ} := by
      intro q
      have h1 := hmemfmt ℓ q
      have h2 := gfmt_testSet (hR₂deg ℓ) (ta := ta ℓ) (tb := tb ℓ) (m₀ := 9 * ηt)
        (m₁ := 9 * B (γ (pk ℓ)) / 4) (by positivity) (by have := hB (γ (pk ℓ)); positivity) q
      have e : {z | (q, z) ∈ A₂ ℓ} = {z | (q, z) ∈ mem ℓ} ∩
          {z | (q, z) ∈ testSet (R₂ ℓ) (ta ℓ) (tb ℓ) (9 * ηt) (9 * B (γ (pk ℓ)) / 4)} := rfl
      rw [e]
      exact gfmt_inter h1 h2
    have hfF : ∀ q, gfmt 7 (Nk ^ ME + (Nk ^ Mmem + 5) + 2 + 1)
        (max (max (max DE (max Dmem 4)) 1) (2 * (incPoly (pderiv 3 (R₂ ℓ))).totalDegree))
        {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F₂ ℓ} := by
      intro q
      have h1 := hE (γ (pk ℓ)) q
      have h2 := gfmt_lift7 (hfA q)
      have h3 := gfmt_timeIcc (ta ℓ) (tb ℓ)
      have h4 := gfmt_le_abs (incPoly (pderiv 3 (R₂ ℓ)))
        (m := B (γ (pk ℓ)) / κ') (div_nonneg hBℓ.le hκ'pos.le)
      have e : {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F₂ ℓ} =
          {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E (γ (pk ℓ))} ∩
          {x₁ : Fin 7 → ℝ | (fun j₁ : Fin 6 => x₁ j₁.castSucc) ∈ {z | (q, z) ∈ A₂ ℓ}} ∩
          {x₁ : Fin 7 → ℝ | ta ℓ ≤ x₁ 6 ∧ x₁ 6 ≤ tb ℓ} ∩
          {x₁ : Fin 7 → ℝ | B (γ (pk ℓ)) / κ' ≤ |eval x₁ (incPoly (pderiv 3 (R₂ ℓ)))|} := by
        ext x₁
        simp only [F₂, subBlock, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
          eval_incPoly _ q x₁]
        tauto
      rw [e]
      exact gfmt_inter (gfmt_inter (gfmt_inter h1 h2) h3) h4
    have hdegI : 2 * (incPoly (pderiv 3 (R₂ ℓ))).totalDegree ≤ 4 := by
      have h1 : (pderiv (3 : Fin 4) (R₂ ℓ)).totalDegree ≤ 1 :=
        totalDegree_pderiv_le' (R₂ ℓ) (3 : Fin 4) (hR₂deg ℓ)
      have := totalDegree_incPoly_le (pderiv 3 (R₂ ℓ))
      omega
    have hpowMi : Nk ^ ME + (Nk ^ Mmem + 5) + 2 + 1 ≤ Nk ^ Mi := by linarith
    have hpowA : Nk ^ Mmem + 5 ≤ Nk ^ Mi := by
      have : 0 ≤ Nk ^ ME := by positivity
      linarith
    refine gchart_subbox hO hNk hMi (hjj ℓ) hκ (R₂ ℓ) r₂ (A₂ ℓ) (F₂ ℓ) ?_ ?_ ?_ (hR₂deg ℓ)
      (hcoef ℓ) ?_ ?_ ?_ hcuℓ hfrℓ
    · intro l hl
      exact hmemA ℓ l hl.1
    · intro l hl t ht
      obtain ⟨-, hts⟩ := hl
      have hw := testSet_whole (hR₂deg ℓ) (subBlock_lt _ _ _ _) hts t ht
      refine ⟨?_, ?_, ?_⟩
      · calc |eval (gx l t) (R₂ ℓ)| ≤ 3 * (9 * ηt) := hw.1
          _ = 27 * ηt := by ring
          _ ≤ κ' * gδ Nk r₂ := hδlo
      · calc |eval (gx l t) (pderiv 3 (R₂ ℓ))| ≤ 9 * B (γ (pk ℓ)) / 4 := hw.2
          _ ≤ κ' * B (γ (pk ℓ)) := by nlinarith
      · have hc := labelTest_curv (hRep ℓ) (hlam ℓ) hηt hBℓ (hlow ℓ) (gx l t)
        have hδ := gδ_pos Nk r₂
        calc |eval (gx l t) (pderiv 3 (pderiv 3 (R₂ ℓ)))| ≤ B (γ (pk ℓ)) ^ 2 / (4 * ηt) := hc
          _ ≤ κ' * B (γ (pk ℓ)) ^ 2 / gδ Nk r₂ := by
            rw [div_le_div_iff₀ (by positivity) hδ]
            have : B (γ (pk ℓ)) ^ 2 * gδ Nk r₂ ≤ B (γ (pk ℓ)) ^ 2 * (4 * κ' * ηt) :=
              mul_le_mul_of_nonneg_left hδhi (by positivity)
            nlinarith
    · intro p hp
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
    · exact measurableSet_of_slices6 fun q => measurableSet_of_gfmt (hfA q)
    · exact measurableSet_of_slices7 fun q => measurableSet_of_gfmt (hfF q)
    · intro q
      refine ⟨gfmt_mono hpowA ((le_max_right DE (max Dmem 4)).trans hDi) (hfA q),
        gfmt_mono hpowMi ?_ (hfF q)⟩
      refine max_le (max_le (max_le (le_max_left _ _ |>.trans hDi) ?_) ?_) ?_
      · exact (le_max_right _ _).trans hDi
      · omega
      · exact hdegI.trans ((le_max_right _ _).trans ((le_max_right _ _).trans hDi))
  -- assemble
  refine preImprovementAt_of_family r₂ (T i + s₀) (fun ℓ => γ (pk ℓ)) j₂
    (fun ℓ => c (pk ℓ) + Matrix.toEuclideanLin (Q (pk ℓ)) (boxCenter s₀ (bx ℓ)))
    (fun ℓ => u (pk ℓ)) (fun ℓ => subFrame (Q (pk ℓ)) s₀) R₂ A₂ F₂ lst' hdepth himp hcard ?_
    hlst hlstm hchart ?_
  · intro ℓ ℓ' hne' hγ hj
    have hj' : subIdx s₀ (j (pk ℓ)) (jj ℓ) = subIdx s₀ (j (pk ℓ')) (jj ℓ') := by
      have := congrArg Fin.val hj
      simpa using this
    exact (hdisj ℓ ℓ' hne' hγ hj').mono Set.inter_subset_left Set.inter_subset_left
  · refine hsucc.trans (Finset.sum_le_sum fun ℓ _ => ?_)
    refine mul_le_mul_right (measure_mono ?_) _
    intro p hp
    obtain ⟨hpE, hpg, hpt, hpl⟩ := hp
    obtain ⟨hA, hder⟩ := hgoodA ℓ p.1 hpg
    refine ⟨⟨hpE, hA, hpt, ?_⟩, hpl⟩
    have := hder p.2 hpt
    have hBℓ := hB (γ (pk ℓ))
    calc B (γ (pk ℓ)) / κ' ≤ B (γ (pk ℓ)) / 4 :=
          div_le_div_of_nonneg_left hBℓ.le (by norm_num) (by linarith)
      _ ≤ _ := this

end Submission.Obl.k4_clean_cover_graph_atlas
