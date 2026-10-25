import Submission.Obl.k4_pair_bin_atlas_assembly.Charts
import Submission.Obl.k4_pair_bin_atlas_assembly.FrozenPairs
import Submission.Obl.k4_quadratic_atlas_normalization.StepInterface

/-!
# Charts from the frozen pairs

The seam between the original-law selection (`FrozenPairs`) and the physical charts
(`Choice.roughAt`):

* `nodeEligible`: the representative of a key, in model coordinates, and its hidden derivative
  are small at the three block nodes; a measurable trajectory condition fixed before the time
  freezing;
* `lift`: the analytic kernel's short-interval bounds imply `nodeEligible` (quadratic
  extrapolation from the short interval to the whole block);
* `roughAt_of_frozen`: frozen pairs built with `nodeEligible` give a rough system at the index,
  the observation lists being the old lists composed with the neighbouring bins.
-/

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Submission.Obl.k4_quadratic_atlas_normalization MvPolynomial MeasureTheory Set
open scoped ENNReal

/-- The bins within distance one of a bin, coordinatewise. -/
noncomputable def nbhd {d : ℕ} (β' : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Finset.univ.image (fun o : Fin d → Fin 3 => fun i => β' i + ((o i : ℕ) : ℤ) - 1)

theorem card_nbhd_le {d : ℕ} (β' : Fin d → ℤ) : (nbhd β').card ≤ 3 ^ d :=
  Finset.card_image_le.trans (by simp)

theorem mem_nbhd {d : ℕ} {β β' : Fin d → ℤ} (h : ∀ i, |β i - β' i| ≤ 1) : β ∈ nbhd β' := by
  refine Finset.mem_image.mpr ⟨fun i => ⟨(β i - β' i + 1).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have := h i; rw [abs_le] at this; omega
  · funext i
    have := h i
    rw [abs_le] at this
    simp only
    omega

namespace PairData

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ} {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε) {Cs : ℕ} (k : BinKernel Cs)

/-- The bins neighbouring the bins of a witness. -/
noncomputable def nbrBins (α : EuclideanSpace ℝ (Fin 3)) (s' : Fin p.m) :
    Finset (Fin k.d → ℤ) :=
  (p.bins k α s').biUnion nbhd

theorem card_nbrBins_le (α : EuclideanSpace ℝ (Fin 3)) (s' : Fin p.m) :
    (p.nbrBins k α s').card ≤ 2 * 3 ^ k.d := by
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum fun β' _ => card_nbhd_le β').trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (k.card_le _ _ _ _ _)

/-- The representative test of a key at an anchor, in model coordinates. -/
noncomputable def physRep (θ : AnchorParameter) (b : Fin p.J) (β : Fin k.d → ℤ) :
    MvPolynomial (Fin 4) ℝ :=
  phys p.T (p.jr b) p.κ (p.c b) (p.u b) (p.Q b) (Bk (p.γ b))
    (p.representativeTest (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) b β)

/-- The representative of a key and its hidden derivative are small at the three block
nodes. -/
def nodeEligible (a' : ℝ) (θ : AnchorParameter) (b : Fin p.J) (β : Fin k.d → ℤ) :
    Set Trajectory :=
  {l | ∀ i : Fin 3,
    |eval (x l (node p.T (p.jr b) i)) (p.physRep k θ b β)| ≤ δ Nk L * Nk ^ a' / 8 ∧
    |eval (x l (node p.T (p.jr b) i)) (pderiv (3 : Fin 4) (p.physRep k θ b β))| ≤
      Bk (p.γ b) * Nk ^ a' / 8}

theorem measurableSet_nodeEligible (a' : ℝ) (θ : AnchorParameter) (b : Fin p.J)
    (β : Fin k.d → ℤ) : MeasurableSet (p.nodeEligible k a' θ b β) := by
  unfold nodeEligible
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => ?_
  rw [Set.ofPred_and]
  exact (measurableSet_le (measurable_eval_x _ _).abs measurable_const).inter
    (measurableSet_le (measurable_eval_x _ _).abs measurable_const)

theorem representativeTest_tests (θ : AnchorParameter) (b : Fin p.J) (β : Fin k.d → ℤ)
    (hN : 0 ≤ Nk) :
    (p.representativeTest (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) b β).totalDegree ≤ 2 ∧
      (∀ e, |(p.representativeTest (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) b β).coeff e| ≤
        Nk ^ M) ∧
      |eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4)
        (p.representativeTest (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) b β)))| ≤
        (δ Nk L)⁻¹ := by
  unfold representativeTest
  rcases p.representative (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) b β with _ | r
  · refine ⟨by simp, fun e => by simp; positivity, ?_⟩
    simp only [map_zero, abs_zero]
    have : 0 < δ Nk L := by unfold δ; positivity
    positivity
  · obtain ⟨h1, h2, h3, -⟩ := p.tests r
    exact ⟨h1, h2, h3⟩

/-- The analytic kernel's short-interval bounds imply the node eligibility. -/
theorem lift (hN : 1 ≤ Nk) (hBpos : ∀ γ, 0 < Bk γ) {a' : ℝ} (hCR : Nk ^ (-(k.CR * a)) ≤ 1 / 2)
    (hgap : 256 * Nk ^ ((k.CK + 2 * k.CR) * a) ≤ Nk ^ a') (θ : AnchorParameter)
    (s : Fin p.m) (v : PairPoint) (hv : v ∈ p.H s) (β : Fin k.d → ℤ) (r : Fin p.m)
    (hr : p.representative (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) β = some r)
    (hshort : p.shortBounds k s v (p.P r)) :
    v.1 ∈ p.nodeEligible k a' θ (p.frame s) β := by
  have hNpos : 0 < Nk := lt_of_lt_of_le one_pos hN
  have hrep : p.physRep k θ (p.frame s) β =
      phys p.T (p.jr (p.frame s)) p.κ (p.c (p.frame s)) (p.u (p.frame s)) (p.Q (p.frame s))
        (Bk (p.γ (p.frame s))) (p.P r) := by
    unfold physRep
    rw [p.representativeTest_eq _ _ _ hr]
  have hdeg : (p.P r).totalDegree ≤ 2 := (p.tests r).1
  have hq : (0 : ℝ) < 2 ^ p.T := by positivity
  set η : ℝ := Nk ^ (-(k.CR * a)) / (2 : ℝ) ^ p.T with hη
  have hηpos : 0 < η := by rw [hη]; exact div_pos (Real.rpow_pos_of_pos hNpos _) hq
  have hlen : ((p.jr (p.frame s) + 1) / (2 : ℝ) ^ p.T - p.jr (p.frame s) / (2 : ℝ) ^ p.T) =
      1 / (2 : ℝ) ^ p.T := by field_simp; ring
  have hη2 : 2 * η ≤ (p.jr (p.frame s) + 1) / (2 : ℝ) ^ p.T - p.jr (p.frame s) / (2 : ℝ) ^ p.T := by
    rw [hlen, hη]
    rw [show 2 * (Nk ^ (-(k.CR * a)) / (2 : ℝ) ^ p.T) = (2 * Nk ^ (-(k.CR * a))) / (2 : ℝ) ^ p.T
      by ring]
    gcongr
    linarith
  have hratio : ((p.jr (p.frame s) + 1) / (2 : ℝ) ^ p.T - p.jr (p.frame s) / (2 : ℝ) ^ p.T) / η =
      Nk ^ (k.CR * a) := by
    rw [hlen, hη, Real.rpow_neg hNpos.le]
    field_simp
  have hpow : 32 * Nk ^ (k.CK * a) * (Nk ^ (k.CR * a)) ^ 2 =
      32 * Nk ^ ((k.CK + 2 * k.CR) * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, mul_assoc, ← Real.rpow_add hNpos]
    congr 2
    push_cast
    ring
  have ht₀ : v.2.1 ∈ Set.Icc (p.jr (p.frame s) / (2 : ℝ) ^ p.T)
      ((p.jr (p.frame s) + 1) / (2 : ℝ) ^ p.T) := p.source_time s hv
  have hB : 0 < Bk (p.γ (p.frame s)) := hBpos _
  intro i
  have hnode : node p.T (p.jr (p.frame s)) i ∈ Set.Icc (p.jr (p.frame s) / (2 : ℝ) ^ p.T)
      ((p.jr (p.frame s) + 1) / (2 : ℝ) ^ p.T) := node_mem_tblock _ _ i
  constructor
  · rw [hrep]
    have hb := interval_bound_of_short
      (quadratic_eval_x (phys p.T (p.jr (p.frame s)) p.κ (p.c (p.frame s)) (p.u (p.frame s))
        (p.Q (p.frame s)) (Bk (p.γ (p.frame s))) (p.P r)) ((totalDegree_phys_le _).trans hdeg) v.1)
      ht₀ hηpos hη2 (X := δ Nk L * Nk ^ (k.CK * a)) (fun t ht hdist => by
        rw [eval_phys]
        exact (hshort t ht hdist).1) _ hnode
    rw [hratio] at hb
    have hδ : 0 < δ Nk L := by unfold δ; positivity
    calc _ ≤ 32 * (δ Nk L * Nk ^ (k.CK * a)) * (Nk ^ (k.CR * a)) ^ 2 := hb
      _ = δ Nk L * (32 * Nk ^ (k.CK * a) * (Nk ^ (k.CR * a)) ^ 2) := by ring
      _ = δ Nk L * (32 * Nk ^ ((k.CK + 2 * k.CR) * a)) := by rw [hpow]
      _ ≤ δ Nk L * (Nk ^ a' / 8) := by gcongr; linarith
      _ = δ Nk L * Nk ^ a' / 8 := by ring
  · rw [hrep]
    have hd1 : (pderiv (3 : Fin 4) (phys p.T (p.jr (p.frame s)) p.κ (p.c (p.frame s))
        (p.u (p.frame s)) (p.Q (p.frame s)) (Bk (p.γ (p.frame s))) (p.P r))).totalDegree ≤ 2 :=
      (Submission.Obl.k4_eligibility_sign_description.degree_pderiv_le _ _).trans
        ((totalDegree_phys_le _).trans hdeg)
    have hb := interval_bound_of_short (quadratic_eval_x _ hd1 v.1)
      ht₀ hηpos hη2 (X := Bk (p.γ (p.frame s)) * Nk ^ (k.CK * a)) (fun t ht hdist => by
        rw [eval_pderiv_phys, abs_mul, abs_of_pos hB]
        exact mul_le_mul_of_nonneg_left (hshort t ht hdist).2 hB.le) _ hnode
    rw [hratio] at hb
    calc _ ≤ 32 * (Bk (p.γ (p.frame s)) * Nk ^ (k.CK * a)) * (Nk ^ (k.CR * a)) ^ 2 := hb
      _ = Bk (p.γ (p.frame s)) * (32 * Nk ^ (k.CK * a) * (Nk ^ (k.CR * a)) ^ 2) := by ring
      _ = Bk (p.γ (p.frame s)) * (32 * Nk ^ ((k.CK + 2 * k.CR) * a)) := by rw [hpow]
      _ ≤ Bk (p.γ (p.frame s)) * (Nk ^ a' / 8) := by gcongr; linarith
      _ = Bk (p.γ (p.frame s)) * Nk ^ a' / 8 := by ring

/-- The frozen choices of a `FrozenPairs` record, as chart choices. -/
noncomputable def frozenChoice {CD a' : ℝ}
    (fp : p.FrozenPairs k CD (p.nodeEligible k a')) : p.Choice where
  d := k.d
  R0 := p.representativeTest (p.bins k fp.θ.1) fp.θ.1 ((Nk ^ a) ^ (-(Cs : ℝ)))
  coin := fp.coin
  nbr := p.nbrBins k fp.θ.1
  t := fp.time

/-- **Frozen pairs give a rough system at the index.** -/
theorem roughAt_of_frozen {CD a' : ℝ} (fp : p.FrozenPairs k CD (p.nodeEligible k a'))
    (hN : 1 ≤ Nk) {M' D' Me De : ℕ} {κ' Z : ℝ}
    (hKn : p.κ * (2 * 3 ^ k.d : ℕ) ≤ κ') (hM' : M ≤ M')
    (hB : ∀ γ, 0 < Bk γ ∧ Bk γ ≤ Z) (hZM : Nk ^ M ≤ Z) (hZT : (2 : ℝ) ^ p.T ≤ Z)
    (hcoef : 81 * Nk ^ M * (6 * Z ^ 2) ^ 2 ≤ Nk ^ M')
    (hρD : (κ' * Nk ^ a')⁻¹ ≤ Nk ^ (-(CD * a)))
    (hEm : ∀ γ, MeasurableSet (Ek γ))
    (hEf : ∀ γ i, fmt 7 (Nk ^ Me) De
      {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ Ek γ})
    (hbudA : (p.m : ℝ) * Nk ^ M + 14 ≤ Nk ^ M')
    (hbudF : Nk ^ Me + (((p.m : ℝ) * Nk ^ M + 14) + (2 + (p.m : ℝ) * Nk ^ M)) ≤ Nk ^ M')
    (hD' : max De (max D 2) ≤ D')
    (hmass : ENNReal.ofReal κ'⁻¹ ≤
      ∑ s, ENNReal.ofReal (ωk (p.world s)) * p.incidenceLaw s (fp.F s)) :
    RoughBody Nk Wk ωk νk Ek Bk L a' M' D' κ' p.T := by
  classical
  let C := p.frozenChoice k fp
  have hNpos : 0 < Nk := lt_of_lt_of_le one_pos hN
  refine C.roughAt hN (Kn := 2 * 3 ^ k.d) (ρD := Nk ^ (-(CD * a))) (Z := Z) hKn
    (Nat.one_le_iff_ne_zero.mpr (by positivity)) (fun s' => p.card_nbrBins_le k fp.θ.1 s') hM'
    hB hZM hZT hcoef (fun key => p.representativeTest_tests k fp.θ key.1 key.2 hNpos.le) hρD
    fp.time_mem hEm hEf hbudA hbudF hD' fp.F fp.F_measurable ?_ fp.F_source hmass
  intro s v hv
  obtain ⟨hE, hT⟩ := fp.F_target s v hv
  refine ⟨hE, ⟨⟨s, ⟨rfl, rfl⟩, fp.F_source s v hv⟩, fp.F_eligible s v hv, ?_⟩, hT, ?_⟩
  · -- the discriminant floor at the frozen source time
    obtain ⟨r, hr, hfloor⟩ := fp.F_representative s v hv
    show Bk (p.γ (p.frame s)) ^ 2 * Nk ^ (-(CD * a)) ≤
      |eval (x v.1 (fp.time (p.j (p.frame s)))) (discPoly (phys p.T (p.jr (p.frame s)) p.κ
        (p.c (p.frame s)) (p.u (p.frame s)) (p.Q (p.frame s)) (Bk (p.γ (p.frame s)))
        (p.representativeTest (p.bins k fp.θ.1) fp.θ.1 ((Nk ^ a) ^ (-(Cs : ℝ)))
          (p.frame s) (fp.coin s))))|
    rw [p.representativeTest_eq _ _ _ hr, eval_discPoly, disc_phys _ (p.tests r).1, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hfloor (sq_nonneg _)
  · -- the observable neighbour compatibility
    obtain ⟨s', hs', hfr, β', hβ', hnear⟩ := fp.F_compatible s v hv
    refine ⟨s', hs', hfr, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨β', hβ', mem_nbhd hnear⟩

end PairData

/-- A rough body at a slack `κ ≤ N ^ ε` and a horizon `2 ^ T ≤ N ^ (h + ε)` is a sample of the
accepted rough system. -/
theorem RoughBody.roughAt {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ} {L a h : ℝ} {M D : ℕ} {ε κ : ℝ} {T : ℕ}
    (hR : RoughBody Nk Wk ωk νk Ek Bk L a M D κ T) (hκ1 : 1 ≤ κ) (hκε : κ ≤ Nk ^ ε)
    (hT : (2 : ℝ) ^ T ≤ Nk ^ (h + ε)) :
    Submission.Obl.k4_quadratic_atlas_normalization.RoughAt Nk Wk ωk νk Ek Bk L a h M D ε := by
  obtain ⟨C', γ, j, c, u, Q, R, A, F, lst, h1, h2, h3, h4, h5⟩ := hR
  exact ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst, hT, h1, h2, h3, h4, h5⟩

end Submission.Obl.k4_pair_bin_atlas_assembly
