import Submission.Obl.k4_narrow_projected_row_parents.Cmp.AllParentSheets

/-!
# Native sheets of all true parents, eventually

`Cmp.SheetComparison.all_parents_native_sheets` (o200, x0864) needs, at one index, fine
physical meshes `δ₀, δ₁` with their pure base caps and native-bin caps, and zoomed meshes
`σ₀, σ₁` small against fixed powers of the loss and of the parent filling. For a fixed
loss exponent `A` all of them hold eventually along a valid prepared sequence, with
`σ₀ = N^(-(s e + 1))`, `σ₁ = N^(-(s e + s + 1))`, `δᵢ = N^(-(tᵢ + (κ + ℓ) s + 1))`,
`e = α A + β`.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Metric Set Filter MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

noncomputable section

/-- A fixed power of a subpower loss is eventually below `N`. -/
theorem eventually_const_mul_pow_le {N K : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    (hN1 : ∀ k, 1 ≤ N k) (hK1 : ∀ k, 1 ≤ K k)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε) (c : ℝ) (hc : 0 ≤ c) (j e : ℕ) :
    ∀ᶠ k in atTop, (c * K k ^ j) ^ e ≤ N k := by
  have hj : (0 : ℝ) < 2 * (j * e + 1) := by positivity
  have hε : (0 : ℝ) < 1 / (2 * (j * e + 1)) := by positivity
  have hbig : ∀ᶠ k in atTop, (max c 1) ^ e ≤ N k ^ ((1 : ℝ) / 2) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hN).eventually_ge_atTop _
  filter_upwards [hK _ hε, hbig] with k hk hb
  have hNk := hN1 k
  have hN0 : 0 < N k := lt_of_lt_of_le one_pos hNk
  have hKk := hK1 k
  have hpow : K k ^ (j * e) ≤ N k ^ ((j * e : ℝ) * (1 / (2 * (j * e + 1)))) := by
    calc K k ^ (j * e) ≤ (N k ^ (1 / (2 * ((j : ℝ) * e + 1)))) ^ (j * e) := by
          gcongr
      _ = N k ^ ((j * e : ℝ) * (1 / (2 * (j * e + 1)))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hexp : (j * e : ℝ) * (1 / (2 * (j * e + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hj]; nlinarith [show (0 : ℝ) ≤ j * e by positivity]
  have hpow' : K k ^ (j * e) ≤ N k ^ ((1 : ℝ) / 2) :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hNk hexp)
  have hcK : 0 ≤ c * K k ^ j := by positivity
  calc (c * K k ^ j) ^ e ≤ (max c 1 * K k ^ j) ^ e := by
        gcongr
        exact le_max_left _ _
    _ = (max c 1) ^ e * K k ^ (j * e) := by rw [mul_pow, ← pow_mul]
    _ ≤ N k ^ ((1 : ℝ) / 2) * N k ^ ((1 : ℝ) / 2) := by
        gcongr
    _ = N k := by rw [← Real.rpow_add hN0]; norm_num

/-- The mesh, cap and numeric hypotheses of `all_parents_native_sheets` at one index, for the
power exponent `e` (`= α A + β`). -/
def NativeMeshHyps {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (e : ℕ) (δ₀ σ₀ δ₁ σ₁ : ℝ) : Prop :=
  0 < δ₀ ∧ 0 < σ₀ ∧ 0 < δ₁ ∧ 0 < σ₁ ∧
  δ₀ * (2 * p.K k + 2) ≤ σ₀ * (16 * p.K k * a.q k s * narrow p k s) ∧
  δ₁ * (2 * p.K k + 2) ≤ σ₁ * (16 * p.K k * a.q k s * narrow p k s) ∧
  (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ e * σ₀ ≤ 1 ∧
  (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ e * σ₁ ≤ width p k s ∧
  (2 * p.K k * parentBinCap (p.K k)) ^ e * σ₁ ≤ 1 ∧
  (∀ q : Fin 3 → ℤ, a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₀
      (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q} ≤
    ENNReal.ofReal ((4 * p.K k + 2) * p.K k * δ₀ ^ 3)) ∧
  (∀ (q : Fin 3 → ℤ) (x₀ : ℤ), a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
      (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q ∧
      ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋ = x₀} ≤
    ENNReal.ofReal (p.K k * width p k s ^ p.d * δ₁ ^ 3))

/-- **The native-sheet hypotheses hold eventually**, at `σ₀ = N^(-(s e + 1))`,
`σ₁ = N^(-(s e + s + 1))`, `δᵢ = σᵢ N^(-((κ + ℓ) s + 1))`, together with the atlas. -/
theorem eventually_native_mesh_hyps (e : ℕ) {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatl : a.Atlases p) {s : ℝ} (hs : 0 < s) (hsU : s ≤ p.U) :
    ∃ R : ℝ, 1 < R ∧ ∀ᶠ k in atTop, a.AtlasAt p R k s ∧
      NativeMeshHyps p a k s e (p.N k ^ (-((s * e + 1) + (p.kappa + p.ell) * s + 1)))
        (p.N k ^ (-(s * e + 1))) (p.N k ^ (-((s * e + s + 1) + (p.kappa + p.ell) * s + 1)))
        (p.N k ^ (-(s * e + s + 1))) := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have hK1 : ∀ k, 1 ≤ p.K k := hp.2.2.1.1
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hd0 : 0 ≤ p.d := hp.2.2.2.1
  set t₀ : ℝ := s * e + 1 with ht₀
  set t₁ : ℝ := s * e + s + 1 with ht₁
  set r₀ : ℝ := t₀ + (p.kappa + p.ell) * s + 1 with hr₀
  set r₁ : ℝ := t₁ + (p.kappa + p.ell) * s + 1 with hr₁
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hse : 0 ≤ s * e := mul_nonneg hs.le he0
  have hκℓs : 0 < (p.kappa + p.ell) * s := mul_pos (by linarith) hs
  set R : ℝ := s⁻¹ + p.U + r₀ + r₁ + 2 with hR
  have hsinv : 0 < s⁻¹ := inv_pos.mpr hs
  have hU0 : 0 < p.U := hp.2.2.2.2.2.2.2.2.2.2.1
  have hR1 : 1 < R := by linarith
  have hR0 : 0 < R := by linarith
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1.le
  have hRs : R⁻¹ ≤ s := by rw [inv_le_comm₀ hR0 hs]; linarith
  have hr₀R : r₀ ≤ R := by linarith
  have hr₁R : r₁ ≤ R := by linarith
  have hr₀1 : R⁻¹ ≤ r₀ := by linarith
  have hr₁1 : R⁻¹ ≤ r₁ := by linarith
  have hsR : s ≤ R := by
    have : s ≤ p.U := hsU
    linarith
  refine ⟨R, hR1, ?_⟩
  filter_upwards [hatl R hR1, eventually_pure_base_caps p hp a hcommon hcaps hR1, hcaps R hR1,
    hp.2.2.1.2 1 one_pos,
    eventually_const_mul_pow_le hp.2.1 hN1 hK1 hp.2.2.1.2 6000000 (by norm_num) 21 e,
    eventually_const_mul_pow_le hp.2.1 hN1 hK1 hp.2.2.1.2 884736 (by norm_num) 7 e]
    with k hat hpure hcap hKN h2 h3
  have hatk := hat s hRs hsU
  have hN := hN1 k
  have hN0 : 0 < p.N k := lt_of_lt_of_le one_pos hN
  have hK := hK1 k
  have hK0 : 0 < p.K k := lt_of_lt_of_le one_pos hK
  rw [Real.rpow_one] at hKN
  -- the true block length
  have hq : p.N k ^ (-(p.kappa * s)) / p.K k ≤ a.q k s := by
    have hT0 : (0 : ℝ) < (2 : ℝ) ^ a.T k s := by positivity
    have hqd : a.q k s = ((2 : ℝ) ^ a.T k s)⁻¹ := by
      unfold PreparedModel.q; rw [zpow_neg, zpow_natCast]
    have h2' : (2 : ℝ) ^ a.T k s ≤ p.K k * p.N k ^ (p.kappa * s) := hatk.2.1
    rw [hqd, Real.rpow_neg hN0.le, div_le_iff₀ hK0, inv_mul_eq_div, le_div_iff₀ hT0]
    calc (p.N k ^ (p.kappa * s))⁻¹ * (2 : ℝ) ^ a.T k s ≤ (p.N k ^ (p.kappa * s))⁻¹ *
          (p.K k * p.N k ^ (p.kappa * s)) := by gcongr
      _ = p.K k := by field_simp
  -- the zoomed meshes against the physical ones
  have hres : ∀ t r : ℝ, r = t + (p.kappa + p.ell) * s + 1 →
      p.N k ^ (-r) * (2 * p.K k + 2) ≤
        p.N k ^ (-t) * (16 * p.K k * a.q k s * narrow p k s) := by
    intro t r hr
    have hgs : narrow p k s = p.N k ^ (-(p.ell * s)) := by
      unfold narrow; congr 1; ring
    have hlow : 16 * p.N k * p.N k ^ (-r) ≤ p.N k ^ (-t) * (16 * p.K k * a.q k s * narrow p k s) := by
      have h0 : p.N k ^ (-r) = p.N k ^ (-t) * (p.N k ^ (-(p.kappa * s)) *
          p.N k ^ (-(p.ell * s))) * (p.N k)⁻¹ := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_neg_one,
          ← Real.rpow_add hN0]
        congr 1; rw [hr]; ring
      have h1 : p.N k * p.N k ^ (-r) = p.N k ^ (-t) * (p.N k ^ (-(p.kappa * s)) *
          p.N k ^ (-(p.ell * s))) := by
        rw [h0]; field_simp
      calc 16 * p.N k * p.N k ^ (-r) = 16 * (p.N k * p.N k ^ (-r)) := by ring
        _ = 16 * (p.N k ^ (-t) * (p.N k ^ (-(p.kappa * s)) * p.N k ^ (-(p.ell * s)))) := by
          rw [h1]
        _ = p.N k ^ (-t) * (16 * p.K k * (p.N k ^ (-(p.kappa * s)) / p.K k) *
            p.N k ^ (-(p.ell * s))) := by field_simp
        _ ≤ p.N k ^ (-t) * (16 * p.K k * a.q k s * narrow p k s) := by
          rw [hgs]; gcongr
    have hNr : 0 ≤ p.N k ^ (-r) := Real.rpow_nonneg hN0.le _
    calc p.N k ^ (-r) * (2 * p.K k + 2) ≤ p.N k ^ (-r) * (16 * p.N k) := by
          gcongr; linarith
      _ = 16 * p.N k * p.N k ^ (-r) := by ring
      _ ≤ _ := hlow
  -- the filling and bin powers
  have hfill : (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ e =
      (6000000 * p.K k ^ 21) ^ e * p.N k ^ (s * e) := by
    have hw : width p k s = p.N k ^ (-s) := rfl
    have h1 : 2 * p.K k * (3000000 * p.K k ^ 20 / p.N k ^ (-s)) =
        6000000 * p.K k ^ 21 * p.N k ^ s := by
      rw [Real.rpow_neg hN0.le]; field_simp; ring
    rw [parentFilling, hw, h1, mul_pow, ← Real.rpow_natCast (p.N k ^ s) e,
      ← Real.rpow_mul hN0.le]
  have hbin : 2 * p.K k * parentBinCap (p.K k) = 884736 * p.K k ^ 7 := by
    rw [parentBinCap]; ring
  have hpos2 : 0 ≤ (6000000 * p.K k ^ 21) ^ e := by positivity
  have hNse : 0 < p.N k ^ (s * e) := Real.rpow_pos_of_pos hN0 _
  refine ⟨hatk, Real.rpow_pos_of_pos hN0 _, Real.rpow_pos_of_pos hN0 _,
    Real.rpow_pos_of_pos hN0 _, Real.rpow_pos_of_pos hN0 _, hres t₀ r₀ rfl, hres t₁ r₁ rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- (2K filling)^e σ₀ ≤ 1
    rw [hfill]
    have e1 : p.N k ^ (s * e) * p.N k ^ (-t₀) = (p.N k)⁻¹ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_neg_one]; congr 1; rw [ht₀]; ring
    calc (6000000 * p.K k ^ 21) ^ e * p.N k ^ (s * e) * p.N k ^ (-t₀)
        = (6000000 * p.K k ^ 21) ^ e * (p.N k)⁻¹ := by rw [mul_assoc, e1]
      _ ≤ p.N k * (p.N k)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hN0.ne'
  · -- (2K filling)^e σ₁ ≤ a_s
    rw [hfill]
    have e1 : p.N k ^ (s * e) * p.N k ^ (-t₁) = p.N k ^ (-s) * (p.N k)⁻¹ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; rw [ht₁]; ring
    have hw : width p k s = p.N k ^ (-s) := rfl
    rw [hw]
    calc (6000000 * p.K k ^ 21) ^ e * p.N k ^ (s * e) * p.N k ^ (-t₁)
        = (6000000 * p.K k ^ 21) ^ e * (p.N k ^ (-s) * (p.N k)⁻¹) := by rw [mul_assoc, e1]
      _ ≤ p.N k * (p.N k ^ (-s) * (p.N k)⁻¹) := by
          gcongr
      _ = p.N k ^ (-s) := by field_simp
  · -- (2K binCap)^e σ₁ ≤ 1
    rw [hbin]
    have ht1 : 1 ≤ t₁ := by rw [ht₁]; nlinarith
    have hNt : p.N k ^ (-t₁) ≤ (p.N k)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    calc (884736 * p.K k ^ 7) ^ e * p.N k ^ (-t₁) ≤ p.N k * (p.N k)⁻¹ := by
          gcongr
      _ = 1 := mul_inv_cancel₀ hN0.ne'
  · -- pure base caps at δ₀
    exact hpure r₀ hr₀1 hr₀R
  · -- native-bin caps at δ₁
    intro q x₀
    have h := (hcap r₁ s 1 hr₁1 hr₁R hs.le hsR hRinv1 hR1.le).2.1 true q x₀
    have hcell : ∀ z : α × ℝ, a.cell (p.N k) r₁ k z =
        Submission.Lib.K4MovingMeshBoxes.baseMesh (p.N k ^ (-r₁))
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) := fun z => rfl
    simp only [hcell, if_true] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    have hw : width p k s = p.N k ^ (-s) := rfl
    rw [hw, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (p.N k ^ (-r₁)), ← Real.rpow_mul hN0.le,
      mul_assoc, ← Real.rpow_add hN0]
    congr 1; push_cast; ring


/-- **Native sheets of all true parents at depth `s`, eventually.** -/
theorem eventually_all_parents_native_sheets (A : ℕ) {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatl : a.Atlases p) {s : ℝ} (hs : 0 < s) (hsU : s ≤ p.U) :
    ∃ αc βc : ℕ, 1 ≤ βc ∧ ∀ᶠ k in atTop,
      ∃ (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
        (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) (E : Set (α × ℝ)),
        (∀ i, Rel i ≠ 0 ∧ (Rel i).totalDegree ≤ 4) ∧ MeasurableSet E ∧
        a.mu k E ≤ ENNReal.ofReal (p.K k *
          (((2 * p.K k * parentFilling (p.K k) (width p k s)) ^ A)⁻¹ +
            ((2 * p.K k * parentBinCap (p.K k)) ^ A)⁻¹)) ∧
        ∀ i, ∀ᵐ z ∂a.mu k, z ∈ a.parentSet k s i → z ∉ E →
          SheetOn (Rel i) (g i (branch ((a.parentSupportZoom p k s i).push (a.F k s i))
              (rootBaseCoordinates (parentZoomPoint p a k s i z))
              (parentZoomPoint p a k s i z 3)))
            (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z)))
            (4 * ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹)
            ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc)) ∧
          |eval (a.x k z.1 z.2) (a.P k) -
            (g i (branch ((a.parentSupportZoom p k s i).push (a.F k s i))
              (rootBaseCoordinates (parentZoomPoint p a k s i z))
              (parentZoomPoint p a k s i z 3))
              (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))))).re| ≤
            32 * (2 * p.K k) ^ 9 * width p k s := by
  obtain ⟨αc, βc, hβc, hsheets⟩ := all_parents_native_sheets
  refine ⟨αc, βc, hβc, ?_⟩
  obtain ⟨R, -, hev⟩ := eventually_native_mesh_hyps (αc * A + βc) p hp a hcommon hcaps hatl hs hsU
  filter_upwards [hev] with k ⟨hat, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact hsheets A p hp a hcommon R k s hs.le hat _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

end

end Submission.Obl.k4_narrow_projected_row_parents
