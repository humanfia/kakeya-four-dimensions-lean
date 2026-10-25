-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/GraphAssembly.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0581, commit 793edcb4e591,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GraphAssembly.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Assembly
import Submission.Obl.k4_clean_cover_graph_atlas.RootTests
import Submission.Obl.k4_clean_cover_graph_atlas.Certificates

/-!
# From a label system to a graph atlas

The `GraphAtlas` certificate of `Certificates.lean` from a label system: each label has an old
path chart (packet) at the greedy level, a sub-block `jj < 2^{s₀}`, a box `bx`, a representative
quadratic `P` with scale `s`, a member set `mem` in Boolean format, and a set `good ⊆ mem` of lines
in the root test set of `(P, s)`; lists and their success on good incidences are given.
The charts keep the scaled old frames (`Frames`), the lines are `mem ∩ rootTestSet`, the incidences
are the incidences of `E` on these lines in the sub-block, and every line of a chart gets its
root certificate from `root_certificate`.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The per-chart clause of a graph atlas. -/
def GraphChart (Nk L : ℝ) (Bv : ℝ) (Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (r₀ h θ β : ℝ) (M D T : ℕ) (jb : ℕ) (cb ub : EuclideanSpace ℝ (Fin 2))
    (Qb : Matrix (Fin 2) (Fin 2) ℝ) (Pb : MvPolynomial (Fin 4) ℝ) (sb : ℝ)
    (Ab : Set (ℕ × (Fin 6 → ℝ))) (Fb : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) : Prop :=
  Matrix.det Qb ≠ 0 ∧
    ‖cb‖ + ‖ub‖ ≤ Nk ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, (|Qb e e'| + |Qb⁻¹ e e'|)) ≤ Nk ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |Qb e e'|) ≤ Nk ^ β / (2 : ℝ) ^ T ∧
    Pb.totalDegree ≤ 2 ∧ (∀ e, |Pb.coeff e| ≤ Nk ^ M) ∧
    0 < sb ∧ sb ≤ Nk ^ M ∧ sb⁻¹ ≤ Nk ^ M ∧
    MeasurableSet Ab ∧ MeasurableSet Fb ∧
    (∀ i, fmt 6 (Nk ^ M) D {z | (i, z) ∈ Ab} ∧
      fmt 7 (Nk ^ M) D {z : Fin 7 → ℝ | ((i, fun a : Fin 6 => z a.castSucc), z 6) ∈ Fb}) ∧
    (∀ l ∈ Ab, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧
      ∀ t ∈ Set.Icc ((jb : ℝ) / (2 : ℝ) ^ T) (((jb : ℝ) + 1) / (2 : ℝ) ^ T),
        ‖Matrix.toEuclideanLin Qb⁻¹ (y l t - cb - t • ub)‖ ≤ Nk ^ β) ∧
    (∀ p ∈ Fb, p ∈ Ev ∧ p.1 ∈ Ab ∧
      p.2 ∈ Set.Icc ((jb : ℝ) / (2 : ℝ) ^ T) (((jb : ℝ) + 1) / (2 : ℝ) ^ T)) ∧
    (∀ l ∈ Ab, ∀ t ∈ Set.Icc ((jb : ℝ) / (2 : ℝ) ^ T) (((jb : ℝ) + 1) / (2 : ℝ) ^ T),
      ∃ w₀ : ℝ,
        |(x l t) 3 - w₀| ≤ δ Nk r₀ / Bv * Nk ^ (-(θ * h * L)) ∧
        MvPolynomial.eval (Function.update (x l t) (3 : Fin 4) w₀) Pb = 0 ∧
        sb / 2 ≤ |MvPolynomial.eval (Function.update (x l t) (3 : Fin 4) w₀)
          (MvPolynomial.pderiv (3 : Fin 4) Pb)| ∧
        |MvPolynomial.eval (Function.update (x l t) (3 : Fin 4) w₀)
          (MvPolynomial.pderiv (3 : Fin 4) Pb)| ≤ 2 * sb)

/-- A graph atlas from any finite label type; the `Fin` indexing is built here. -/
theorem graphAtlas_of_family {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {B : Fin W → ℝ} {r₀ h θ β : ℝ} {M D T : ℕ} {ι : Type*} [Fintype ι]
    (γ₂ : ι → Fin W) (j₂ : ι → Fin (2 ^ T)) (c₂ u₂ : ι → EuclideanSpace ℝ (Fin 2))
    (Q₂ : ι → Matrix (Fin 2) (Fin 2) ℝ) (P₂ : ι → MvPolynomial (Fin 4) ℝ) (s₂ : ι → ℝ)
    (A₂ : ι → Set (ℕ × (Fin 6 → ℝ))) (F₂ : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset ι)
    (hcard : (Fintype.card ι : ℝ) ≤ Nk ^ M)
    (hB : ∀ w, 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M)
    (hdisj : ∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b'))
    (hlst : ∀ w o, ((lst w o).card : ℝ) ≤ Nk ^ β)
    (hlstm : ∀ w b, MeasurableSet {o | b ∈ lst w o})
    (hchart : ∀ b, GraphChart Nk L (B (γ₂ b)) (E (γ₂ b)) r₀ h θ β M D T (j₂ b : ℕ) (c₂ b) (u₂ b)
      (Q₂ b) (P₂ b) (s₂ b) (A₂ b) (F₂ b))
    (hmass : ENNReal.ofReal (Nk ^ (-β)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) *
      ((ν (γ₂ b)).prod volume) {p | p ∈ F₂ b ∧ b ∈ lst (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)}) :
    ∃ (C₂ : ℕ) (γ₃ : Fin C₂ → Fin W) (j₃ : Fin C₂ → Fin (2 ^ T))
      (c₃ u₃ : Fin C₂ → EuclideanSpace ℝ (Fin 2)) (Q₃ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
      (P₃ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (s₃ : Fin C₂ → ℝ)
      (A₃ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ))) (F₃ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₃ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
      GraphAtlas Nk L W ω ν E B r₀ h θ β M D T C₂ γ₃ j₃ c₃ u₃ Q₃ P₃ s₃ A₃ F₃ lst₃ := by
  classical
  set e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, γ₂ ∘ e.symm, j₂ ∘ e.symm, c₂ ∘ e.symm, u₂ ∘ e.symm, Q₂ ∘ e.symm,
    P₂ ∘ e.symm, s₂ ∘ e.symm, A₂ ∘ e.symm, F₂ ∘ e.symm,
    fun w o => (lst w o).map e.toEmbedding, hcard, hB, ?_, ?_, ?_, ?_, ?_⟩
  · intro b b' hbb' hγ hj
    exact hdisj (e.symm b) (e.symm b') (fun h => hbb' (e.symm.injective h)) hγ hj
  · intro w o
    simp only [Finset.card_map]
    exact hlst w o
  · intro w b
    have : {o | b ∈ (lst w o).map e.toEmbedding} = {o | e.symm b ∈ lst w o} := by
      ext o
      simp only [Set.mem_ofPred_eq, Finset.mem_map_equiv]
    rw [this]
    exact hlstm w (e.symm b)
  · intro b
    exact hchart (e.symm b)
  · calc ENNReal.ofReal (Nk ^ (-β)) ≤ _ := hmass
      _ = ∑ b, ENNReal.ofReal (ω ((γ₂ ∘ e.symm) b)) * ((ν ((γ₂ ∘ e.symm) b)).prod volume)
            {p | p ∈ (F₂ ∘ e.symm) b ∧ b ∈ (lst ((γ₂ ∘ e.symm) b)
              (obs (B ((γ₂ ∘ e.symm) b)) (δ Nk L) p)).map e.toEmbedding} := by
          refine (Fintype.sum_equiv e.symm _ _ (fun b => ?_)).symm
          simp only [Function.comp_apply, Finset.mem_map_equiv]

/-- The root-test threshold of a label. -/
noncomputable def rootThreshold (Nk r₀ h θ L Bv sb : ℝ) : ℝ :=
  sb * gδ Nk r₀ * Nk ^ (-(θ * h * L)) / (4 * Bv)

/-- One graph chart inside an old path chart: scaled old frame on a sub-box, lines cut by the
root test, incidences of `E` on them in the sub-block. -/
theorem graphChart_subbox {Nk L : ℝ} {M D Mp Dp : ℕ} {κ : ℝ} {Ti : ℕ} {j₀ : ℕ} {rold Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop} {r₀ h θ β : ℝ}
    {ME DE Dmem : ℕ} {Hmem : ℝ}
    (hO : gchart Nk Mp Dp κ Ti (j₀ : ℝ) rold Bv Ev c u Q R A F ex) (hNk : 1 ≤ Nk)
    {s₀ jj : ℕ} (hjj : jj < 2 ^ s₀) (bx : Fin 2 → ℤ)
    (P : MvPolynomial (Fin 4) ℝ) (sb m₀ : ℝ) (mem : Set (ℕ × (Fin 6 → ℝ)))
    (hBv : 0 < Bv)
    (hEf : ∀ q, gfmt 7 (Nk ^ ME) DE
      {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ Ev})
    (hP : P.totalDegree ≤ 2) (hPcoef : ∀ e, |P.coeff e| ≤ Nk ^ M)
    (hs : 0 < sb ∧ sb ≤ Nk ^ M ∧ sb⁻¹ ≤ Nk ^ M)
    (hm₀ : 0 ≤ m₀) (hm₀le : m₀ ≤ rootThreshold Nk r₀ h θ L Bv sb)
    (hcurv : |qc P| * m₀ ≤ sb ^ 2 / 40)
    (hmemA : ∀ l ∈ mem, l ∈ A ∧ inBox s₀ bx (zc Q c u l (subMid Ti s₀ j₀ jj)))
    (hmemfmt : ∀ q, gfmt 6 Hmem Dmem {z | (q, z) ∈ mem})
    (hne : mem.Nonempty)
    (hκ : κ + 1 ≤ Nk ^ β) (hMp : Mp ≤ M) (hcu : Nk ^ Mp + κ * (κ + 1) ≤ Nk ^ M)
    (hfr : (side s₀)⁻¹ * Nk ^ Mp ≤ Nk ^ M)
    (hfmtM : Nk ^ ME + Hmem + 11 + 3 ≤ Nk ^ M) (hD : max DE (max Dmem 4) ≤ D) :
    GraphChart Nk L Bv Ev r₀ h θ β M D (Ti + s₀) (subIdx s₀ j₀ jj)
      (c + Matrix.toEuclideanLin Q (boxCenter s₀ bx)) u (subFrame Q s₀) P sb
      (mem ∩ rootTestSet P sb m₀
        ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (Ti + s₀)) (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)))
      {p | p ∈ Ev ∧ p.1 ∈ mem ∩ rootTestSet P sb m₀
        ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (Ti + s₀)) (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀))
        ∧ p.2 ∈ subBlock Ti s₀ j₀ jj} := by
  set ta := (subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (Ti + s₀)
  set tb := ((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)
  set A₂ := mem ∩ rootTestSet P sb m₀ ta tb with hA₂
  have hdet : Q.det ≠ 0 := hO.1
  have hpowMp : Nk ^ Mp ≤ Nk ^ M := pow_le_pow_right₀ hNk hMp
  have hab : ta < tb := subBlock_lt Ti s₀ j₀ jj
  -- formats
  have hfA : ∀ q, gfmt 6 (Hmem + 11) (max Dmem 4) {z | (q, z) ∈ A₂} := by
    intro q
    have h := gfmt_inter (hmemfmt q) (gfmt_rootTestSet hP (s := sb) (ta := ta) (tb := tb) hm₀ q)
    exact h
  have hfF : ∀ q, gfmt 7 (Nk ^ ME + (Hmem + 11) + 2) (max (max DE (max Dmem 4)) 1)
      {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈
        {p : (ℕ × (Fin 6 → ℝ)) × ℝ | p ∈ Ev ∧ p.1 ∈ A₂ ∧ p.2 ∈ subBlock Ti s₀ j₀ jj}} := by
    intro q
    have h := gfmt_inter (gfmt_inter (hEf q) (gfmt_lift7 (hfA q))) (gfmt_timeIcc ta tb)
    have e : {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈
        {p : (ℕ × (Fin 6 → ℝ)) × ℝ | p ∈ Ev ∧ p.1 ∈ A₂ ∧ p.2 ∈ subBlock Ti s₀ j₀ jj}} =
        {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ Ev} ∩
          {x₁ : Fin 7 → ℝ | (fun j₁ : Fin 6 => x₁ j₁.castSucc) ∈ {z | (q, z) ∈ A₂}} ∩
          {x₁ : Fin 7 → ℝ | ta ≤ x₁ 6 ∧ x₁ 6 ≤ tb} := by
      ext x₁
      simp only [subBlock, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc]
      tauto
    rw [e]
    exact h
  have hpA : Hmem + 11 ≤ Nk ^ M := by
    have : 0 ≤ Nk ^ ME := by positivity
    linarith
  have hpF : Nk ^ ME + (Hmem + 11) + 2 ≤ Nk ^ M := by linarith
  obtain ⟨l₀, hl₀⟩ := hne
  obtain ⟨hl₀A, hl₀box⟩ := hmemA l₀ hl₀
  have h0 := hO
  obtain ⟨-, -, -, hQs, -, -, -, -, -, hAl, -⟩ := h0
  refine ⟨det_subFrame_ne_zero hdet s₀,
    (subCenter_norm_le hO hjj hl₀A hl₀box).trans hcu,
    (subFrame_complexity_le hdet s₀ hO.2.2.1).trans hfr, ?_, hP, hPcoef, hs.1, hs.2.1, hs.2.2,
    measurableSet_of_slices6 fun q => measurableSet_of_gfmt (hfA q),
    measurableSet_of_slices7 fun q => measurableSet_of_gfmt (hfF q),
    fun q => ⟨gfmt_mono hpA ((le_max_right DE (max Dmem 4)).trans hD) (hfA q),
      gfmt_mono hpF (max_le hD ((by norm_num : 1 ≤ 4).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans hD)))) (hfF q)⟩, ?_, ?_, ?_⟩
  · rw [sum_abs_subFrame]
    have hsd := side_pos s₀
    have hκ0 : 0 ≤ κ := by
      have := (hAl l₀ hl₀A).2.2 _ (subblock_subset hjj (subMid_mem Ti s₀ j₀ jj))
      exact (norm_nonneg _).trans this.1
    calc side s₀ * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ side s₀ * (κ / (2 : ℝ) ^ Ti) :=
          mul_le_mul_of_nonneg_left hQs hsd.le
      _ = κ / (2 : ℝ) ^ (Ti + s₀) := by unfold side; rw [pow_add]; field_simp
      _ ≤ Nk ^ β / (2 : ℝ) ^ (Ti + s₀) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
  · intro l hl
    obtain ⟨hlA, hbox⟩ := hmemA l hl.1
    obtain ⟨h1, h2, -⟩ := hAl l hlA
    refine ⟨h1.trans hpowMp, fun e => (h2 e).trans hpowMp, fun t ht => ?_⟩
    exact (subFrame_bound hO hlA hbox ht).trans hκ
  · intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  · intro l hl t ht
    obtain ⟨w₀, hw, hz, hd1, hd2⟩ := root_certificate hP hs.1 hm₀ hcurv hab hl.2 ht
    refine ⟨w₀, ?_, hz, hd1, hd2⟩
    calc |(x l t) 3 - w₀| ≤ 4 * m₀ / sb := hw
      _ ≤ 4 * rootThreshold Nk r₀ h θ L Bv sb / sb := by
          gcongr
          exact hs.1.le
      _ = δ Nk r₀ / Bv * Nk ^ (-(θ * h * L)) := by
          rw [rootThreshold]
          simp only [δ, gδ]
          have := hs.1.ne'
          field_simp

/-- **A graph atlas from a label system.** -/
theorem graphAtlas_of_labels
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {r₀ h θ β : ℝ} {M D : ℕ}
    {C : ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {ex : Fin C → Prop} {κ : ℝ} {Mp Dp : ℕ} {Ti : ℕ} {rold : ℝ}
    {ι : Type} [Fintype ι] (pk : ι → Fin C) (jj : ι → ℕ) (bx : ι → Fin 2 → ℤ)
    (P : ι → MvPolynomial (Fin 4) ℝ) (s m₀ : ι → ℝ) (mem good : ι → Set (ℕ × (Fin 6 → ℝ)))
    (lst' : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset ι) (s₀ : ℕ)
    {ME DE Dmem : ℕ} {Hmem : ℝ}
    (hNk : 1 ≤ Nk) (hB : ∀ w, 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M)
    (hE : ∀ w q, gfmt 7 (Nk ^ ME) DE
      {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E w})
    (hold : ∀ ℓ, gchart Nk Mp Dp κ Ti (j (pk ℓ) : ℝ) rold (B (γ (pk ℓ))) (E (γ (pk ℓ)))
      (c (pk ℓ)) (u (pk ℓ)) (Q (pk ℓ)) (R (pk ℓ)) (A (pk ℓ)) (F (pk ℓ)) (ex (pk ℓ)))
    (hjlt : ∀ ℓ, j (pk ℓ) < 2 ^ Ti)
    (hjj : ∀ ℓ, jj ℓ < 2 ^ s₀)
    (hP : ∀ ℓ, (P ℓ).totalDegree ≤ 2) (hPcoef : ∀ ℓ e, |(P ℓ).coeff e| ≤ Nk ^ M)
    (hs : ∀ ℓ, 0 < s ℓ ∧ s ℓ ≤ Nk ^ M ∧ (s ℓ)⁻¹ ≤ Nk ^ M)
    (hm₀ : ∀ ℓ, 0 ≤ m₀ ℓ ∧ m₀ ℓ ≤ rootThreshold Nk r₀ h θ L (B (γ (pk ℓ))) (s ℓ))
    (hcurv : ∀ ℓ, |qc (P ℓ)| * m₀ ℓ ≤ s ℓ ^ 2 / 40)
    (hmemA : ∀ ℓ, ∀ l ∈ mem ℓ, l ∈ A (pk ℓ) ∧
      inBox s₀ (bx ℓ) (zc (Q (pk ℓ)) (c (pk ℓ)) (u (pk ℓ)) l (subMid Ti s₀ (j (pk ℓ)) (jj ℓ))))
    (hmemfmt : ∀ ℓ q, gfmt 6 Hmem Dmem {z | (q, z) ∈ mem ℓ})
    (hne : ∀ ℓ, (mem ℓ).Nonempty)
    (hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → γ (pk ℓ) = γ (pk ℓ') →
      subIdx s₀ (j (pk ℓ)) (jj ℓ) = subIdx s₀ (j (pk ℓ')) (jj ℓ') → Disjoint (mem ℓ) (mem ℓ'))
    (hgood : ∀ ℓ, good ℓ ⊆ mem ℓ ∩ rootTestSet (P ℓ) (s ℓ) (m₀ ℓ)
      ((subIdx s₀ (j (pk ℓ)) (jj ℓ) : ℝ) / (2 : ℝ) ^ (Ti + s₀))
      (((subIdx s₀ (j (pk ℓ)) (jj ℓ) : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)))
    (hlst : ∀ w o, ((lst' w o).card : ℝ) ≤ Nk ^ β)
    (hlstm : ∀ w ℓ, MeasurableSet {o | ℓ ∈ lst' w o})
    (hsucc : ENNReal.ofReal (Nk ^ (-β)) ≤ ∑ ℓ, ENNReal.ofReal (ω (γ (pk ℓ))) *
      ((ν (γ (pk ℓ))).prod volume) {p | p ∈ E (γ (pk ℓ)) ∧ p.1 ∈ good ℓ ∧
        p.2 ∈ subBlock Ti s₀ (j (pk ℓ)) (jj ℓ) ∧
        ℓ ∈ lst' (γ (pk ℓ)) (obs (B (γ (pk ℓ))) (δ Nk L) p)})
    (hκ : κ + 1 ≤ Nk ^ β) (hMp : Mp ≤ M) (hcu : Nk ^ Mp + κ * (κ + 1) ≤ Nk ^ M)
    (hfr : (side s₀)⁻¹ * Nk ^ Mp ≤ Nk ^ M)
    (hfmtM : Nk ^ ME + Hmem + 11 + 3 ≤ Nk ^ M) (hD : max DE (max Dmem 4) ≤ D)
    (hcard : (Fintype.card ι : ℝ) ≤ Nk ^ M) :
    ∃ (C₂ : ℕ) (γ₃ : Fin C₂ → Fin W) (j₃ : Fin C₂ → Fin (2 ^ (Ti + s₀)))
      (c₃ u₃ : Fin C₂ → EuclideanSpace ℝ (Fin 2)) (Q₃ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
      (P₃ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (s₃ : Fin C₂ → ℝ)
      (A₃ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ))) (F₃ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₃ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
      GraphAtlas Nk L W ω ν E B r₀ h θ β M D (Ti + s₀) C₂ γ₃ j₃ c₃ u₃ Q₃ P₃ s₃ A₃ F₃ lst₃ := by
  classical
  let j₂ : ι → Fin (2 ^ (Ti + s₀)) := fun ℓ =>
    ⟨subIdx s₀ (j (pk ℓ)) (jj ℓ), subIdx_lt (hjlt ℓ) (hjj ℓ)⟩
  let A₂ : ι → Set (ℕ × (Fin 6 → ℝ)) := fun ℓ =>
    mem ℓ ∩ rootTestSet (P ℓ) (s ℓ) (m₀ ℓ)
      ((subIdx s₀ (j (pk ℓ)) (jj ℓ) : ℝ) / (2 : ℝ) ^ (Ti + s₀))
      (((subIdx s₀ (j (pk ℓ)) (jj ℓ) : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀))
  let F₂ : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun ℓ =>
    {p | p ∈ E (γ (pk ℓ)) ∧ p.1 ∈ A₂ ℓ ∧ p.2 ∈ subBlock Ti s₀ (j (pk ℓ)) (jj ℓ)}
  refine graphAtlas_of_family (fun ℓ => γ (pk ℓ)) j₂
    (fun ℓ => c (pk ℓ) + Matrix.toEuclideanLin (Q (pk ℓ)) (boxCenter s₀ (bx ℓ)))
    (fun ℓ => u (pk ℓ)) (fun ℓ => subFrame (Q (pk ℓ)) s₀) P s A₂ F₂ lst' hcard hB ?_ hlst hlstm
    (fun ℓ => graphChart_subbox (hold ℓ) hNk (hjj ℓ) (bx ℓ) (P ℓ) (s ℓ) (m₀ ℓ) (mem ℓ)
      (hB (γ (pk ℓ))).1 (hE (γ (pk ℓ))) (hP ℓ) (hPcoef ℓ) (hs ℓ) (hm₀ ℓ).1 (hm₀ ℓ).2 (hcurv ℓ)
      (hmemA ℓ) (hmemfmt ℓ)
      (hne ℓ) hκ hMp hcu hfr hfmtM hD) ?_
  · intro ℓ ℓ' hne' hγ hj
    have hj' : subIdx s₀ (j (pk ℓ)) (jj ℓ) = subIdx s₀ (j (pk ℓ')) (jj ℓ') := by
      have := congrArg Fin.val hj
      simpa [j₂] using this
    exact (hdisj ℓ ℓ' hne' hγ hj').mono Set.inter_subset_left Set.inter_subset_left
  · refine hsucc.trans (Finset.sum_le_sum fun ℓ _ => ?_)
    refine mul_le_mul_right (measure_mono ?_) _
    intro p hp
    obtain ⟨hpE, hpg, hpt, hpl⟩ := hp
    exact ⟨⟨hpE, hgood ℓ hpg, hpt⟩, hpl⟩

end Submission.Obl.k4_clean_cover_graph_atlas
