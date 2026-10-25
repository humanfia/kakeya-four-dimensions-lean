/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactAtlas.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactStructure

/-!
# Atlases of the zoomed contact instance at one index

`zoom_T_bounds`: the zoomed block count `2^(T_s - T_r)` is within `K² N^(κδ)`
of `N^(κσ)`.

`zoom_atlasAt`: at one index and one depth `σ` of the grid range, the zoomed
model satisfies every atlas condition of the frozen prepared model with a
constant `Kz` dominating the explicit losses: `K² N^((κ+d+ℓ)δ)` from the grid,
`2·4^M/θ` from pruning, the witness bound for the box constants, `K M₁ N^(ℓδ)`
from the row normalization and `K N^δ` from the fits.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- Bounds for the zoomed block count. -/
theorem zoom_T_bounds (hp : p.Valid) {R : ℝ} (hatr : a.AtlasAt p R I.k r) {j : Fin I.M}
    (hats : a.AtlasAt p R I.k (I.depth j)) (hTle : a.T I.k r ≤ a.T I.k (I.depth j)) {σ : ℝ}
    (h1 : 0 ≤ σ - (I.depth j - r)) (h2 : σ - (I.depth j - r) ≤ I.δ) :
    p.N I.k ^ (p.kappa * σ) / (p.K I.k ^ 2 * p.N I.k ^ (p.kappa * I.δ)) ≤
        (2 : ℝ) ^ (a.T I.k (I.depth j) - a.T I.k r) ∧
      (2 : ℝ) ^ (a.T I.k (I.depth j) - a.T I.k r) ≤ p.K I.k ^ 2 * p.N I.k ^ (p.kappa * σ) := by
  have hN := (hp.1 I.k)
  have hN0 : 0 < p.N I.k := by linarith
  have hN1 : 1 ≤ p.N I.k := by linarith
  have hK := hp.2.2.1.1 I.k
  have hK0 : 0 < p.K I.k := by linarith
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hpow : (2 : ℝ) ^ (a.T I.k (I.depth j) - a.T I.k r) =
      (2 : ℝ) ^ a.T I.k (I.depth j) / (2 : ℝ) ^ a.T I.k r := by
    rw [pow_sub₀ _ (by norm_num) hTle, div_eq_mul_inv]
  rw [hpow]
  have hs1 := hats.1
  have hs2 := hats.2.1
  have hr1 := hatr.1
  have hr2 := hatr.2.1
  have hTr : (0 : ℝ) < (2 : ℝ) ^ a.T I.k r := by positivity
  have hTs : (0 : ℝ) < (2 : ℝ) ^ a.T I.k (I.depth j) := by positivity
  set u := I.depth j - r
  have hsr : p.N I.k ^ (p.kappa * I.depth j) = p.N I.k ^ (p.kappa * u) * p.N I.k ^ (p.kappa * r) := by
    rw [← Real.rpow_add hN0]; congr 1; simp only [u]; ring
  have hσu : p.N I.k ^ (p.kappa * σ) ≤ p.N I.k ^ (p.kappa * u) * p.N I.k ^ (p.kappa * I.δ) := by
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith
  have huσ : p.N I.k ^ (p.kappa * u) ≤ p.N I.k ^ (p.kappa * σ) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith
  have hNr : 0 < p.N I.k ^ (p.kappa * r) := Real.rpow_pos_of_pos hN0 _
  have hNu : 0 < p.N I.k ^ (p.kappa * u) := Real.rpow_pos_of_pos hN0 _
  have hNδ : 0 < p.N I.k ^ (p.kappa * I.δ) := Real.rpow_pos_of_pos hN0 _
  constructor
  · rw [div_le_div_iff₀ (by positivity) hTr]
    calc p.N I.k ^ (p.kappa * σ) * (2 : ℝ) ^ a.T I.k r
        ≤ (p.N I.k ^ (p.kappa * u) * p.N I.k ^ (p.kappa * I.δ)) *
            (p.K I.k * p.N I.k ^ (p.kappa * r)) :=
          mul_le_mul hσu hr2 hTr.le (by positivity)
      _ = (p.K I.k ^ 2 * p.N I.k ^ (p.kappa * I.δ)) *
            (p.N I.k ^ (p.kappa * I.depth j) / p.K I.k) := by
          rw [hsr]; field_simp
      _ ≤ (p.K I.k ^ 2 * p.N I.k ^ (p.kappa * I.δ)) * (2 : ℝ) ^ a.T I.k (I.depth j) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = _ := by ring
  · rw [div_le_iff₀ hTr]
    calc (2 : ℝ) ^ a.T I.k (I.depth j) ≤ p.K I.k * p.N I.k ^ (p.kappa * I.depth j) := hs2
      _ = p.K I.k ^ 2 * p.N I.k ^ (p.kappa * u) * (p.N I.k ^ (p.kappa * r) / p.K I.k) := by
          rw [hsr]; field_simp
      _ ≤ p.K I.k ^ 2 * p.N I.k ^ (p.kappa * σ) * (2 : ℝ) ^ a.T I.k r := by
          apply mul_le_mul _ hr1 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left huσ (by positivity)

end ZoomInput

/-- Parameters of the zoomed instance. -/
def zoomParams (p : Parameters) {a : PreparedModel α} {r : ℝ} (I : ℕ → ZoomInput p a r)
    (Kz : ℕ → ℝ) (U' e₀' : ℝ) : Parameters :=
  ⟨fun m => p.N (I m).k, Kz, p.d, p.kappa, p.ell, p.S, U', e₀'⟩

set_option maxHeartbeats 1600000 in
/-- **Zoomed atlas at one index and depth.** -/
theorem zoom_atlasAt {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {r : ℝ} (I : ℕ → ZoomInput p a r) (hM : ∀ m, 0 < (I m).M)
    (Kz : ℕ → ℝ) (U' e₀' : ℝ) (m : ℕ) {R R' M₁ σ vs : ℝ}
    (hatr : a.AtlasAt p R (I m).k r) (hats : ∀ j, a.AtlasAt p R (I m).k ((I m).depth j))
    (hnest : ∀ j j' : Fin (I m).M, j < j' → ∀ i : Fin (a.n (I m).k ((I m).depth j')),
      ∃ h : Fin (a.n (I m).k ((I m).depth j)),
        a.A (I m).k ((I m).depth j') i ⊆ a.A (I m).k ((I m).depth j) h ∧
          a.block (I m).k ((I m).depth j') i ⊆ a.block (I m).k ((I m).depth j) h)
    (hnestr : ∀ j : Fin (I m).M, ∀ i : Fin (a.n (I m).k ((I m).depth j)),
      ∃ h : Fin (a.n (I m).k r), a.A (I m).k ((I m).depth j) i ⊆ a.A (I m).k r h ∧
        a.block (I m).k ((I m).depth j) i ⊆ a.block (I m).k r h)
    (hGm : MeasurableSet (I m).G) (hGsub : (I m).G ⊆ a.B (I m).k r (I m).Q ×ˢ
      a.block (I m).k r (I m).Q)
    (hθ : 0 < (I m).θ) (hlam : (I m).lam ≠ 0) (hlamM : |(I m).lam⁻¹| ≤ M₁)
    (hBle : |(I m).B 0| + |(I m).B 1| ≤ M₁) (hM₁ : 1 ≤ M₁)
    (hTle : ∀ j, a.T (I m).k r ≤ a.T (I m).k ((I m).depth j))
    (hδ : 0 < (I m).δ) (hσ1 : (I m).δ ≤ σ) (hσ2 : σ ≤ (((I m).M : ℝ) + 1) * (I m).δ)
    (hvs1 : R⁻¹ ≤ vs) (hvs2 : vs ≤ R)
    (hpis : ∀ m' : ℤ, a.pi (I m).k {w | ⌊w / p.N (I m).k ^ (-vs)⌋ = m'} ≤
      ENNReal.ofReal (p.K (I m).k * p.N (I m).k ^ (-p.S * vs)))
    (hgaps : ∀ j : Fin (I m).M, 3 * (p.K (I m).k * (p.K (I m).k * p.N (I m).k ^ (-p.S * vs))) <
      (I m).θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2)
    (hR'1 : R⁻¹ ≤ R'⁻¹) (hR'2 : R' ≤ R)
    (hKz1 : p.K (I m).k ^ 2 * p.N (I m).k ^ ((p.kappa + p.d + p.ell) * (I m).δ) ≤ Kz m)
    (hKz3 : 2 * 4 ^ (I m).M / (I m).θ ≤ Kz m)
    (hKz4 : 4 * p.K (I m).k + M₁ * (4 * p.K (I m).k +
      12 * p.K (I m).k ^ 2 / p.N (I m).k ^ (-vs) + M₁) ≤ Kz m)
    (hKz5 : p.K (I m).k * M₁ * p.N (I m).k ^ ((1 + p.ell) * (I m).δ) ≤ Kz m) :
    (zoomModel I hM).AtlasAt (zoomParams p I Kz U' e₀') R' m σ := by
  classical
  set J := I m with hJ
  have := hcommon.prob J.k
  have hN := hp.1 J.k
  have hN0 : 0 < p.N J.k := by linarith
  have hN1 : 1 ≤ p.N J.k := by linarith
  have hK1 : 1 ≤ p.K J.k := hp.2.2.1.1 J.k
  have hK0 : 0 < p.K J.k := by linarith
  have hd0 : 0 ≤ p.d := hp.2.2.2.1
  have hκ0 : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ0 : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  set jσ := J.lev (hM m) σ
  set s := J.depth jσ
  obtain ⟨hg1, hg2⟩ := J.lev_gap (hM m) hδ hσ1 hσ2
  have hsr : s - r = (((jσ : ℕ) : ℝ) + 1) * J.δ := by simp only [s, ZoomInput.depth]; ring
  rw [← hsr] at hg1 hg2
  -- scale comparisons
  have hNδ0 : 1 ≤ p.N J.k ^ J.δ := Real.one_le_rpow hN1 hδ.le
  have hw : width p J.k s / width p J.k r = p.N J.k ^ (-(s - r)) := by
    simp only [width]; rw [rpow_ratio hN0]; ring_nf
  have hgr : narrow p J.k s / narrow p J.k r = p.N J.k ^ (-(p.ell * (s - r))) := by
    simp only [narrow]; rw [rpow_ratio hN0]; ring_nf
  have hws : p.N J.k ^ (-σ) ≤ p.N J.k ^ (-(s - r)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hws' : p.N J.k ^ (-(s - r)) ≤ p.N J.k ^ J.δ * p.N J.k ^ (-σ) := by
    rw [← Real.rpow_add hN0]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hℓsr : p.ell * (s - r) ≤ p.ell * σ := mul_le_mul_of_nonneg_left (by linarith) hℓ0.le
  have hℓsr' : p.ell * σ ≤ p.ell * (s - r) + p.ell * J.δ := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hℓ0.le
  have hgs : p.N J.k ^ (-p.ell * σ) ≤ p.N J.k ^ (-(p.ell * (s - r))) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by rw [neg_mul]; linarith)
  have hgs' : p.N J.k ^ (-(p.ell * (s - r))) ≤ p.N J.k ^ (p.ell * J.δ) * p.N J.k ^ (-p.ell * σ) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by rw [neg_mul]; linarith)
  -- consequences of the size of `Kz`
  have hexp : (p.kappa + p.d + p.ell) * J.δ = p.kappa * J.δ + (p.d + p.ell) * J.δ := by ring
  have hdl0 : 0 ≤ (p.d + p.ell) * J.δ := mul_nonneg (by linarith) hδ.le
  have hk0 : 0 ≤ p.kappa * J.δ := mul_nonneg hκ0.le hδ.le
  have hpow1 : p.N J.k ^ (p.kappa * J.δ) ≤ p.N J.k ^ ((p.kappa + p.d + p.ell) * J.δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hexp]; linarith)
  have hpow2 : p.N J.k ^ ((p.d + p.ell) * J.δ) ≤ p.N J.k ^ ((p.kappa + p.d + p.ell) * J.δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hexp]; linarith)
  have hKK : p.K J.k ≤ p.K J.k ^ 2 := by
    calc p.K J.k = p.K J.k * 1 := (mul_one _).symm
      _ ≤ p.K J.k * p.K J.k := mul_le_mul_of_nonneg_left hK1 hK0.le
      _ = p.K J.k ^ 2 := (sq _).symm
  have hK2Kz : p.K J.k ^ 2 ≤ Kz m := by
    have h1 : 1 ≤ p.N J.k ^ ((p.kappa + p.d + p.ell) * J.δ) :=
      Real.one_le_rpow hN1 (by rw [hexp]; linarith)
    exact le_trans (le_mul_of_one_le_right (sq_nonneg _) h1) hKz1
  have hKKz : p.K J.k ≤ Kz m := hKK.trans hK2Kz
  have hKz0 : 0 < Kz m := lt_of_lt_of_le hK0 hKKz
  obtain ⟨hT1, hT2⟩ := J.zoom_T_bounds hp hatr (hats jσ) (hTle jσ) hg1 hg2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- lower block count
    show p.N J.k ^ (p.kappa * σ) / Kz m ≤ (2 : ℝ) ^ (a.T J.k s - a.T J.k r)
    refine le_trans ?_ hT1
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_left hpow1 (sq_nonneg _)) hKz1
  · -- upper block count
    show (2 : ℝ) ^ (a.T J.k s - a.T J.k r) ≤ Kz m * p.N J.k ^ (p.kappa * σ)
    exact hT2.trans (mul_le_mul_of_nonneg_right hK2Kz (by positivity))
  · intro i
    exact ⟨(hats jσ).measurable_A _, (hats jσ).measurable_B _, (hats jσ).B_sub_A _⟩
  · intro i i' hii hj
    have hne : (Fintype.equivFin (J.Ret jσ)).symm i ≠ (Fintype.equivFin (J.Ret jσ)).symm i' :=
      fun h => hii ((Fintype.equivFin _).symm.injective h)
    exact J.disjoint_ret (hats jσ) hne (congrArg Fin.val hj)
  · intro i
    set x := (Fintype.equivFin (J.Ret jσ)).symm i
    have hq' : (zoomModel I hM).q m σ = a.q J.k s / a.q J.k r := J.zoom_q x
    have hqr := q_pos a J.k r
    have hqs := q_pos a J.k s
    have hρq0 : 0 ≤ a.q J.k s / a.q J.k r := div_nonneg hqs.le hqr.le
    obtain ⟨hpr1, hpr2⟩ := J.prior_zoom hp hatr (hats jσ) x
    rw [hw, hgr] at hpr1 hpr2
    have hNσ : 0 ≤ p.N J.k ^ (-σ) := Real.rpow_nonneg hN0.le _
    have hNg : 0 ≤ p.N J.k ^ (-p.ell * σ) := Real.rpow_nonneg hN0.le _
    have hwd : (p.N J.k ^ (-σ)) ^ p.d ≤ (p.N J.k ^ (-(s - r))) ^ p.d :=
      Real.rpow_le_rpow hNσ hws hd0
    have hwd' : (p.N J.k ^ (-(s - r))) ^ p.d ≤
        p.N J.k ^ (p.d * J.δ) * (p.N J.k ^ (-σ)) ^ p.d := by
      calc (p.N J.k ^ (-(s - r))) ^ p.d ≤ (p.N J.k ^ J.δ * p.N J.k ^ (-σ)) ^ p.d :=
            Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hws' hd0
        _ = p.N J.k ^ (p.d * J.δ) * (p.N J.k ^ (-σ)) ^ p.d := by
            rw [Real.mul_rpow (Real.rpow_nonneg hN0.le _) hNσ, ← Real.rpow_mul hN0.le, mul_comm J.δ]
    have hwid : width (zoomParams p I Kz U' e₀') m σ = p.N J.k ^ (-σ) := rfl
    have hnar : narrow (zoomParams p I Kz U' e₀') m σ = p.N J.k ^ (-p.ell * σ) := rfl
    have hKz' : (zoomParams p I Kz U' e₀').K m = Kz m := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- prior lower bound
      show ENNReal.ofReal (width (zoomParams p I Kz U' e₀') m σ ^ (zoomParams p I Kz U' e₀').d *
          (zoomModel I hM).q m σ ^ 2 * narrow (zoomParams p I Kz U' e₀') m σ /
            (zoomParams p I Kz U' e₀').K m) ≤
        condPrior (a.nu J.k) (a.A J.k r J.Q) (a.A J.k s x.1.1)
      rw [hq', hwid, hnar, hKz']
      show ENNReal.ofReal ((p.N J.k ^ (-σ)) ^ p.d * (a.q J.k s / a.q J.k r) ^ 2 *
          p.N J.k ^ (-p.ell * σ) / Kz m) ≤ _
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hpr1
      apply div_le_div₀ (by positivity) _ (by positivity) hK2Kz
      apply mul_le_mul (mul_le_mul_of_nonneg_right hwd (sq_nonneg _)) hgs hNg (by positivity)
    · -- prior upper bound
      show condPrior (a.nu J.k) (a.A J.k r J.Q) (a.A J.k s x.1.1) ≤
        ENNReal.ofReal ((zoomParams p I Kz U' e₀').K m *
          width (zoomParams p I Kz U' e₀') m σ ^ (zoomParams p I Kz U' e₀').d *
          (zoomModel I hM).q m σ ^ 2 * narrow (zoomParams p I Kz U' e₀') m σ)
      rw [hq', hwid, hnar, hKz']
      show _ ≤ ENNReal.ofReal (Kz m * (p.N J.k ^ (-σ)) ^ p.d * (a.q J.k s / a.q J.k r) ^ 2 *
          p.N J.k ^ (-p.ell * σ))
      refine le_trans hpr2 (ENNReal.ofReal_le_ofReal ?_)
      have hgle := hgs'
      calc p.K J.k ^ 2 * (p.N J.k ^ (-(s - r))) ^ p.d * (a.q J.k s / a.q J.k r) ^ 2 *
            p.N J.k ^ (-(p.ell * (s - r)))
          ≤ p.K J.k ^ 2 * (p.N J.k ^ (p.d * J.δ) * (p.N J.k ^ (-σ)) ^ p.d) *
              (a.q J.k s / a.q J.k r) ^ 2 * (p.N J.k ^ (p.ell * J.δ) * p.N J.k ^ (-p.ell * σ)) := by
            gcongr
        _ = (p.K J.k ^ 2 * p.N J.k ^ ((p.d + p.ell) * J.δ)) * (p.N J.k ^ (-σ)) ^ p.d *
              (a.q J.k s / a.q J.k r) ^ 2 * p.N J.k ^ (-p.ell * σ) := by
            rw [add_mul, Real.rpow_add hN0]; ring
        _ ≤ Kz m * (p.N J.k ^ (-σ)) ^ p.d * (a.q J.k s / a.q J.k r) ^ 2 *
              p.N J.k ^ (-p.ell * σ) := by
            gcongr
            exact le_trans (mul_le_mul_of_nonneg_left hpow2 (sq_nonneg _)) hKz1
    · -- residual floor
      show ENNReal.ofReal ((zoomModel I hM).q m σ / (zoomParams p I Kz U' e₀').K m) *
          condPrior (a.nu J.k) (a.A J.k r J.Q) (a.A J.k s x.1.1) ≤
        zoomLaw (a.mu J.k) J.keep J.Z.t₀ J.Z.q J.W (a.B J.k s x.1.1 ×ˢ J.zblock x)
      rw [hq', hKz']
      refine le_trans ?_ (J.floor_zoom hp hcommon hatr hats hnest hGm hθ.le x)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      rw [div_eq_mul_inv, mul_comm]
      apply mul_le_mul_of_nonneg_right _ hρq0
      have h4 : (4 : ℝ) ^ (jσ : ℕ) ≤ 4 ^ J.M := pow_le_pow_right₀ (by norm_num) jσ.2.le
      have hKz' : 2 * 4 ^ (jσ : ℕ) / J.θ ≤ Kz m :=
        le_trans (div_le_div_of_nonneg_right (by linarith) hθ.le) hKz3
      rw [inv_le_comm₀ hKz0 (by positivity)]
      calc (J.θ * (1 / 4 : ℝ) ^ (jσ : ℕ) / 2)⁻¹ = 2 * 4 ^ (jσ : ℕ) / J.θ := by
            rw [one_div, inv_pow]; field_simp
        _ ≤ Kz m := hKz'
    · intro e
      show |Zoom.zoomBox J.Z J.B J.lam (a.c J.k s x.1.1) e| ≤ (zoomParams p I Kz U' e₀').K m
      rw [hKz']
      obtain ⟨l, l', hlB, hl'B, hlb, hl'b, hsep⟩ := J.exists_velocity_witnesses hp hcommon hats
        hnest hθ.le x hvs1 hvs2 hpis (hgaps jσ)
      have hlA := (hats jσ).B_sub_A _ hlB
      have hl'A := (hats jσ).B_sub_A _ hl'B
      have hlQ := J.prior_sub x hlA
      have hl'Q := J.prior_sub x hl'A
      have ht : blockStart (a.T J.k s) (a.j J.k s x.1.1) ∈ a.block J.k s x.1.1 :=
        blockStart_mem _ _
      have htQ := J.block_sub x ht
      have htQ' : blockStart (a.T J.k s) (a.j J.k s x.1.1) ∈ Set.Icc J.Z.t₀ (J.Z.t₀ + J.Z.q) := by
        have h := htQ
        change _ ∈ a.block J.k r J.Q at h
        rwa [J.block_eq] at h
      have hqsr : a.q J.k s ≤ a.q J.k r := q_le_of_block_subset (J.block_sub x)
      have hgsr : narrow p J.k s ≤ narrow p J.k r := by
        unfold narrow
        apply Real.rpow_le_rpow_of_exponent_le hN1
        have : r ≤ s := by have := mul_pos (by positivity : (0:ℝ) < ((jσ : ℕ) : ℝ) + 1) hδ; linarith
        nlinarith
      have hg0 := narrow_pos p hp J.k r
      have hgs0 := narrow_pos p hp J.k s
      have hε : 0 < p.N J.k ^ (-vs) := Real.rpow_pos_of_pos hN0 _
      -- boxes of the descendant, enlarged to parent widths
      have hm := (hats jσ).major_box x.1.1 hlA ht
      have hmQ := hatr.major_box J.Q hlQ htQ
      have htr := (hats jσ).transverse_box x.1.1 hlA ht
      have htrQ := hatr.transverse_box J.Q hlQ htQ
      have hs := (hats jσ).strip x.1.1 hlA
      have hsQ := hatr.strip J.Q hlQ
      have hs' := (hats jσ).strip x.1.1 hl'A
      have hsQ' := hatr.strip J.Q hl'Q
      have hKq : p.K J.k * a.q J.k s ≤ p.K J.k * a.q J.k r :=
        mul_le_mul_of_nonneg_left hqsr hK0.le
      have hKqg : p.K J.k * a.q J.k s * narrow p J.k s ≤ p.K J.k * a.q J.k r * narrow p J.k r :=
        mul_le_mul hKq hgsr hgs0.le (by positivity)
      have hKg : p.K J.k * narrow p J.k s ≤ p.K J.k * narrow p J.k r :=
        mul_le_mul_of_nonneg_left hgsr hK0.le
      refine le_trans ?_ hKz4
      exact zoomBox_bound (Z := J.Z) (B := J.B) (lam := J.lam) (c := a.c J.k s x.1.1)
        (cQ := a.c J.k r J.Q) (b := a.b J.k l) (b' := a.b J.k l')
        (t := blockStart (a.T J.k s) (a.j J.k s x.1.1)) (q := a.q J.k r) (g := narrow p J.k r)
        (K := p.K J.k) (M₁ := M₁) (ε := p.N J.k ^ (-vs))
        hqr hg0 hε hK1 (by linarith) rfl rfl rfl rfl rfl rfl htQ'.1 htQ'.2 hBle hlamM
        (hatr.c_le J.Q 1) ((hats jσ).c_le x.1.1 1) (hm.trans hKq) hmQ (htr.trans hKqg) htrQ
        (hs.trans hKg) hsQ (hs'.trans hKg) hsQ' hlb hsep e
    · exact (Zoom.nPush_degree _).trans ((hats jσ).2.2.2.2.1 x.1.1).2.2.2.2.1
    · -- box inequalities
      intro l hl t ht
      obtain ⟨hb1, hb2, hb3⟩ := J.boxes_zoom hp (hats jσ) x hlam hl ht
      have hlam0 : 0 < |J.lam| := abs_pos.mpr hlam
      have hlinv : 1 / |J.lam| ≤ M₁ := by rw [one_div, ← abs_inv]; exact hlamM
      have hδl : p.N J.k ^ (p.ell * J.δ) ≤ p.N J.k ^ ((1 + p.ell) * J.δ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by rw [add_mul, one_mul]; linarith)
      have hKMN : p.K J.k * M₁ * p.N J.k ^ (p.ell * J.δ) ≤ Kz m :=
        le_trans (mul_le_mul_of_nonneg_left hδl (by positivity)) hKz5
      have hρg : p.N J.k ^ (-(p.ell * (s - r))) / |J.lam| ≤
          M₁ * p.N J.k ^ (p.ell * J.δ) * p.N J.k ^ (-p.ell * σ) := by
        rw [div_eq_mul_one_div, mul_comm]
        calc 1 / |J.lam| * p.N J.k ^ (-(p.ell * (s - r)))
            ≤ M₁ * (p.N J.k ^ (p.ell * J.δ) * p.N J.k ^ (-p.ell * σ)) :=
              mul_le_mul hlinv hgs' (by positivity) (by linarith)
          _ = _ := by ring
      rw [hgr] at hb2 hb3
      refine ⟨?_, ?_, ?_⟩
      · show |(Submission.Lib.K4ContactNormalization.point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k l)) t) 1 -
            _ - t * _| ≤ (zoomParams p I Kz U' e₀').K m * (zoomModel I hM).q m σ
        rw [hq', hKz']
        simp only [Submission.Lib.K4ContactNormalization.point, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        exact hb1.trans (mul_le_mul_of_nonneg_right hKKz hρq0)
      · show |(Submission.Lib.K4ContactNormalization.point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k l)) t) 2 -
            _ - t * _ - _ * (Submission.Lib.K4ContactNormalization.point
              (Zoom.nCoeff J.Z J.B J.lam (a.b J.k l)) t) 1| ≤
          (zoomParams p I Kz U' e₀').K m * (zoomModel I hM).q m σ *
            narrow (zoomParams p I Kz U' e₀') m σ
        rw [hq', hKz', hnar]
        simp only [Submission.Lib.K4ContactNormalization.point, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.cons_val, Fin.isValue]
        refine hb2.trans ?_
        calc p.K J.k * (a.q J.k s / a.q J.k r) * p.N J.k ^ (-(p.ell * (s - r))) / |J.lam|
            = p.K J.k * (a.q J.k s / a.q J.k r) * (p.N J.k ^ (-(p.ell * (s - r))) / |J.lam|) := by
              ring
          _ ≤ p.K J.k * (a.q J.k s / a.q J.k r) *
                (M₁ * p.N J.k ^ (p.ell * J.δ) * p.N J.k ^ (-p.ell * σ)) := by gcongr
          _ = (p.K J.k * M₁ * p.N J.k ^ (p.ell * J.δ)) * (a.q J.k s / a.q J.k r) *
                p.N J.k ^ (-p.ell * σ) := by ring
          _ ≤ Kz m * (a.q J.k s / a.q J.k r) * p.N J.k ^ (-p.ell * σ) := by gcongr
      · show |Zoom.nCoeff J.Z J.B J.lam (a.b J.k l) 4 - _ - _ * Zoom.nCoeff J.Z J.B J.lam
            (a.b J.k l) 3| ≤ (zoomParams p I Kz U' e₀').K m * narrow (zoomParams p I Kz U' e₀') m σ
        rw [hKz', hnar]
        refine hb3.trans ?_
        calc p.K J.k * p.N J.k ^ (-(p.ell * (s - r))) / |J.lam|
            = p.K J.k * (p.N J.k ^ (-(p.ell * (s - r))) / |J.lam|) := by ring
          _ ≤ p.K J.k * (M₁ * p.N J.k ^ (p.ell * J.δ) * p.N J.k ^ (-p.ell * σ)) := by gcongr
          _ = (p.K J.k * M₁ * p.N J.k ^ (p.ell * J.δ)) * p.N J.k ^ (-p.ell * σ) := by ring
          _ ≤ Kz m * p.N J.k ^ (-p.ell * σ) := by gcongr
    · -- fits
      intro l hl t ht
      have hf := J.fits_zoom hp (hats jσ) x hlam hl t ht
      rw [hw] at hf
      obtain ⟨hf1, hf2, hf3⟩ := hf
      have hδ1 : p.N J.k ^ J.δ ≤ p.N J.k ^ ((1 + p.ell) * J.δ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by
          rw [add_mul, one_mul]; have := mul_nonneg hℓ0.le hδ.le; linarith)
      have hKN : p.K J.k * p.N J.k ^ J.δ ≤ Kz m := by
        refine le_trans ?_ hKz5
        calc p.K J.k * p.N J.k ^ J.δ ≤ p.K J.k * 1 * p.N J.k ^ ((1 + p.ell) * J.δ) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hδ1 hK0.le
          _ ≤ p.K J.k * M₁ * p.N J.k ^ ((1 + p.ell) * J.δ) := by gcongr
      have hNs : 0 < p.N J.k ^ (-σ) := Real.rpow_pos_of_pos hN0 _
      have hNsr : 0 < p.N J.k ^ (-(s - r)) := Real.rpow_pos_of_pos hN0 _
      refine ⟨?_, ?_, ?_⟩
      · show _ ≤ (zoomParams p I Kz U' e₀').K m * width (zoomParams p I Kz U' e₀') m σ
        rw [hKz', hwid]
        calc _ ≤ p.K J.k * p.N J.k ^ (-(s - r)) := hf1
          _ ≤ p.K J.k * (p.N J.k ^ J.δ * p.N J.k ^ (-σ)) := by gcongr
          _ = (p.K J.k * p.N J.k ^ J.δ) * p.N J.k ^ (-σ) := by ring
          _ ≤ Kz m * p.N J.k ^ (-σ) := by gcongr
      · show _ ≤ (zoomParams p I Kz U' e₀').K m
        exact hf2.trans hKKz
      · show _ ≤ (zoomParams p I Kz U' e₀').K m / width (zoomParams p I Kz U' e₀') m σ
        rw [hKz', hwid]
        calc _ ≤ p.K J.k / p.N J.k ^ (-(s - r)) := hf3
          _ ≤ Kz m / p.N J.k ^ (-σ) := div_le_div₀ hKz0.le hKKz hNs hws
    · -- hidden-derivative lower bound
      filter_upwards [J.dlower_zoom hp hcommon hats hGm hlam x] with z hz hzB hzI
      exact le_trans (inv_anti₀ hK0 hKKz) (hz hzB hzI)
  · -- coverage
    filter_upwards [J.cover_zoom hcommon hatr hats hnest hnestr hGm hGsub jσ] with z hz
    obtain ⟨x, hx1, hx2⟩ := hz
    refine ⟨Fintype.equivFin (J.Ret jσ) x, ?_, ?_⟩
    · show z.1 ∈ a.B J.k s ((Fintype.equivFin (J.Ret jσ)).symm (Fintype.equivFin _ x)).1.1
      rw [Equiv.symm_apply_apply]; exact hx1
    · show z.2 ∈ interval (a.T J.k s - a.T J.k r)
        (relFin (J.block_sub ((Fintype.equivFin (J.Ret jσ)).symm (Fintype.equivFin _ x))))
      rw [Equiv.symm_apply_apply]; exact hx2
  · -- per-label palette
    intro i v v₀ hv1 hv2
    set x := (Fintype.equivFin (J.Ret jσ)).symm i
    have h := J.palette_zoom hp hcommon hatr hats hGm x (hR'1.trans hv1) (hv2.trans hR'2) v₀
    have hq' : (zoomModel I hM).q m σ = a.q J.k s / a.q J.k r := J.zoom_q x
    rw [hq']
    refine h.trans ?_
    show _ ≤ ENNReal.ofReal (Kz m * (a.q J.k s / a.q J.k r)) *
      condPrior (a.nu J.k) (a.A J.k r J.Q) (a.A J.k s x.1.1) *
        a.pi J.k {w | ⌊w / p.N J.k ^ (-v)⌋ = v₀}
    have hle : ENNReal.ofReal (p.K J.k * (a.q J.k s / a.q J.k r)) ≤
        ENNReal.ofReal (Kz m * (a.q J.k s / a.q J.k r)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKKz
        (div_nonneg (q_pos a J.k s).le (q_pos a J.k r).le))
    exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl

end

end Submission.Obl.k4_row_parent_contact_candidates

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem ZoomInput.lev_mono {p : Parameters} {a : PreparedModel α} {r : ℝ}
    (I : ZoomInput p a r) (hM : 0 < I.M) (hδ : 0 < I.δ) {σ τ : ℝ} (h : σ ≤ τ) :
    I.lev hM σ ≤ I.lev hM τ := by
  simp only [ZoomInput.lev, Fin.mk_le_mk]
  apply min_le_min le_rfl
  apply Nat.sub_le_sub_right
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_right h hδ.le

theorem ZoomInput.zblock_mono {p : Parameters} {a : PreparedModel α} {r : ℝ}
    (I : ZoomInput p a r) (hp : p.Valid) {j₁ j₂ : Fin I.M} (x : I.Ret j₂) (y : I.Ret j₁)
    (h : a.block I.k (I.depth j₂) x.1.1 ⊆ a.block I.k (I.depth j₁) y.1.1) :
    I.zblock x ⊆ I.zblock y := by
  intro t ht
  have h1 := I.untime_mem_block x hp ht
  have h2 := h h1
  rw [I.mem_zblock y, I.time_untime' hp] at h2
  exact h2

/-- **Zoomed nesting at one index.** -/
theorem zoom_nested_at {p : Parameters} (hp : p.Valid) {a : PreparedModel α} {r : ℝ}
    (I : ℕ → ZoomInput p a r) (hM : ∀ m, 0 < (I m).M) (m : ℕ) {R : ℝ}
    (hatr : a.AtlasAt p R (I m).k r) (hats : ∀ j, a.AtlasAt p R (I m).k ((I m).depth j))
    (hnest : ∀ j j' : Fin (I m).M, j < j' → ∀ i : Fin (a.n (I m).k ((I m).depth j')),
      ∃ h : Fin (a.n (I m).k ((I m).depth j)),
        a.A (I m).k ((I m).depth j') i ⊆ a.A (I m).k ((I m).depth j) h ∧
          a.block (I m).k ((I m).depth j') i ⊆ a.block (I m).k ((I m).depth j) h)
    (hnestr : ∀ j : Fin (I m).M, ∀ i : Fin (a.n (I m).k ((I m).depth j)),
      ∃ h : Fin (a.n (I m).k r), a.A (I m).k ((I m).depth j) i ⊆ a.A (I m).k r h ∧
        a.block (I m).k ((I m).depth j) i ⊆ a.block (I m).k r h)
    (hθ : 0 < (I m).θ) (hδ : 0 < (I m).δ) {σ τ : ℝ} (hστ : σ ≤ τ)
    (i : Fin ((zoomModel I hM).n m τ)) :
    ∃ h : Fin ((zoomModel I hM).n m σ), (zoomModel I hM).A m τ i ⊆ (zoomModel I hM).A m σ h ∧
      (zoomModel I hM).block m τ i ⊆ (zoomModel I hM).block m σ h := by
  classical
  set J := I m
  set x := (Fintype.equivFin (J.Ret (J.lev (hM m) τ))).symm i
  obtain ⟨y, hA, hI⟩ := J.ret_ancestor hp hatr hats hnest hnestr hθ
    (J.lev_mono (hM m) hδ hστ) x
  refine ⟨Fintype.equivFin (J.Ret (J.lev (hM m) σ)) y, ?_, ?_⟩
  · show a.A J.k (J.depth (J.lev (hM m) τ)) x.1.1 ⊆
      a.A J.k (J.depth (J.lev (hM m) σ))
        ((Fintype.equivFin (J.Ret (J.lev (hM m) σ))).symm (Fintype.equivFin _ y)).1.1
    rw [Equiv.symm_apply_apply]; exact hA
  · show J.zblock x ⊆ J.zblock ((Fintype.equivFin (J.Ret (J.lev (hM m) σ))).symm
      (Fintype.equivFin _ y))
    rw [Equiv.symm_apply_apply]
    exact J.zblock_mono hp x y hI

end

end Submission.Obl.k4_row_parent_contact_candidates
