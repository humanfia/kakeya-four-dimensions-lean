-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.RetainedCoarse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.FineF
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FiberMass
import Submission.WZ.Obl.wz_terminal_grains_restoration.Main
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- Retaining a small-power share of shading mass retains enough balanced
coarse fibres for the Frostman normalization of the restricted cover. -/
theorem retained_coarse_budget {δ θ ε ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z W : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθε : θ ≤ ε / 12)
    (h56 : 56 ≤ δ ^ (-(ε / 4))) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1) (hWT : ∀ i, W i ⊆ T δ (x i) (v i))
    (hmassY : O (δ ^ θ * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ θ n x v Y S Z ρ N y w f True)
    (A : Finset (Fin N))
    (hret : O (δ ^ (ε / 2)) * ∑ i, μ (Y i) ≤
      ∑ i ∈ S.filter (fun i => f i ∈ A), μ (W i)) :
    δ ^ (-θ) * N ≤ δ ^ (-ε) * A.card := by
  classical
  let S' := S.filter (fun i => f i ∈ A)
  have hvol (i : Fin n) : μ (W i) ≤ O (56 * δ ^ 2) :=
    (measure_mono (hWT i)).trans
      (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hδ.le hδ1 _ _ (hv i))
  have hmassE : O (δ ^ (ε / 2) * (δ ^ θ * n * δ ^ 2)) ≤
      O ((S'.card : ℝ) * (56 * δ ^ 2)) := by
    calc
      _ = O (δ ^ (ε / 2)) * O (δ ^ θ * n * δ ^ 2) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)
      _ ≤ O (δ ^ (ε / 2)) * ∑ i, μ (Y i) := mul_le_mul' le_rfl hmassY
      _ ≤ ∑ i ∈ S', μ (W i) := hret
      _ ≤ ∑ _i ∈ S', O (56 * δ ^ 2) := Finset.sum_le_sum (fun i _ => hvol i)
      _ = O ((S'.card : ℝ) * (56 * δ ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simpa only [O, ENNReal.ofReal_natCast] using
          (ENNReal.ofReal_mul (q := 56 * δ ^ 2) (Nat.cast_nonneg S'.card)).symm
  have hmassR : δ ^ (ε / 2) * (δ ^ θ * n * δ ^ 2) ≤
      (S'.card : ℝ) * (56 * δ ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmassE
  have hq (k : Fin N) : q n {i | i ∈ S ∧ f i = k} =
      ((S.filter (fun i => f i = k)).card : ℝ) := by
    have he : {i | i ∈ S ∧ f i = k} = (↑(S.filter (fun i => f i = k)) : Set (Fin n)) := by
      ext i
      simp
    simp only [q, he, Set.ncard_coe_finset]
  have hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      δ ^ (-θ) * (S.filter (fun i => f i = k')).card := by
    intro k k'
    simpa only [hq] using hC.2.2.2.2.2.2.1 k k'
  have hcard : (S'.card : ℝ) * N ≤ A.card * (δ ^ (-θ) * n) := by
    have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.selected_fiber_mass_le
      S A f (fun _ => (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => le_rfl) hbal
    have hh' : (S'.card : ℝ) * N ≤ δ ^ (-θ) * S.card * A.card := by
      simpa only [S', Finset.sum_const, nsmul_eq_mul, mul_one, one_mul, Fintype.card_fin] using hh
    calc
      _ ≤ δ ^ (-θ) * S.card * A.card := hh'
      _ ≤ δ ^ (-θ) * n * A.card := by
        gcongr
        exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
      _ = _ := by ring
  exact WangZahlLot.Obl.wz_terminal_grains_restoration.budget_arith
    hδ hδ1 (Nat.cast_pos.mpr hn) (Nat.cast_nonneg N) hθε hθ h56 hmassR hcard

/-- Restriction and reindexing also allow a refinement of the shadings,
provided the retained coarse cardinality pays for the slab coefficient. -/
theorem cover_restrict_refined {δ h h' ρ ρ' : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (hρρ' : ρ ≤ ρ')
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (A : Finset (Fin N)) (hA : A.Nonempty) (Z' : Fin n → Set V)
    (hZ' : ∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i)
    (hmass : O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ A), μ (Z' i))
    (hcount : δ ^ (-h) * N ≤ δ ^ (-h') * A.card)
    (hX : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' →
      μ (T ρ' (y k) (w k) ∩ T ρ' (y k') (w k')) ≤ 1 / 2 * μ (T ρ' (y k) (w k)))
    (hmult : ∀ i ∈ S, f i ∈ A →
      q N {k | k ∈ A ∧ T δ (x i) (v i) ⊆ T ρ' (y k) (w k)} ≤ δ ^ (-h')) :
    C δ h' n x v Y (S.filter (fun i => f i ∈ A)) (fun i => if f i ∈ A then Z' i else ∅) ρ'
      A.card (fun k => y (rIdx A k)) (fun k => w (rIdx A k)) (rFib A hA f) True := by
  apply cover_restrict' hδ hδ1 hh hρρ' hC A hA Z' hZ' hmass _ hX hmult
  intro u t r hu hr
  have hsub : q N {k | k ∈ A ∧ T ρ' (y k) (w k) ⊆ I ∩ Q u t r} ≤
      q N {k | T ρ (y k) (w k) ⊆ I ∩ Q u t r} :=
    q_le_of_subset (fun k hk => (T_mono_radius hρρ' _ _).trans hk.2)
  calc
    _ ≤ O (q N {k | T ρ (y k) (w k) ⊆ I ∩ Q u t r}) := ENNReal.ofReal_le_ofReal hsub
    _ ≤ O (δ ^ (-h) * N) * μ (I ∩ Q u t r) := hC.2.2.2.2.1 u t r hu hr
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hcount) le_rfl

end WangZahlLot.Obl.wz_coarse_grains_assembly
