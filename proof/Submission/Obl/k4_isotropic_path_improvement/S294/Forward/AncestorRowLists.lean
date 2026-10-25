-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.AncestorRowLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FieldRowLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreOscillation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedBaseComparison
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockGridCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRows

/-!
# Base-only row lists of the ancestor's test

The list conjunct of `Source.RowClauses` asks, in every base cube of radius `θ` of the CHILD `b`,
for at most `K` row bins at the row mesh. The rows of the ancestor `a` are Lipschitz in the
ancestor's clock coordinates `(unsheared base of a, R_a/δ_a)` (x1096's
`Graph.physical_row_regularity` through `NativeAncestor.model_clock_code`), so a child cube
needs a short list of HEIGHTS `R_a/δ_a`. These come from the core entries of a multiscale core
source at a middle depth `mid` between `a` and `b` (the generic form, for the ancestor's test, of
x1037's `FieldRowLists.field_row_lists_of_old_cores`, which is written for the physical parent):

* `localCorePoint_dist_le`: the local core point of a packet is Lipschitz in its unsheared base;
* `ancestor_height_pieces`: inside one kept core entry of the middle packet `b0`, `R_a/δ_a`
  oscillates by at most `2 K⁸ δ_mid/δ_a` plus a Lipschitz term in the CHILD's unsheared base,
  with the clock ratio `h_b/h_mid` (x0943's `CoreEntryData.actual_core_signal_oscillation`);
* `ancestor_row_lists`: at most `(K¹⁰ · 2K^(3R+18)) · 9³` row bins in every child cube
  (x1035's `Qualification.base_row_list_of_height_pieces`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native
open k4_stable_native_signal_oscillation

noncomputable section

/-- The native base of the native cube point is the native cube base of the packet base. -/
theorem nativeBase_packetNativeCubePoint {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ) (p : PathData W)
    (b : Fin p.C) (q : Event) :
    nativeBase (packetNativeCubePoint Nk B p b q) =
      Analytic.nativeCubeBase (3 * p.κ) (ParentSource.packetBase p b q) := by
  rw [← packetNativeCube_base_eq]
  ext j
  fin_cases j <;> rfl

/-- The native cube base contracts distances once its half-width is at least one half. -/
theorem nativeCubeBase_dist_le {κ : ℝ} (hκ : 1 / 2 ≤ κ) (z z' : EuclideanSpace ℝ (Fin 3)) :
    ‖Analytic.nativeCubeBase κ z - Analytic.nativeCubeBase κ z'‖ ≤ ‖z - z'‖ := by
  have h2 : 1 ≤ 2 * κ := by linarith
  have h2pos : 0 < 2 * κ := by linarith
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have hscaled (x y : ℝ) : ((x + κ) / (2 * κ) - (y + κ) / (2 * κ)) ^ 2 ≤ (x - y) ^ 2 := by
    rw [show (x + κ) / (2 * κ) - (y + κ) / (2 * κ) = (x - y) / (2 * κ) by
      field_simp; ring, div_pow]
    exact div_le_self (sq_nonneg _) (one_le_pow₀ h2)
  fin_cases i
  · simp [Analytic.nativeCubeBase]
  · simpa [Analytic.nativeCubeBase] using hscaled (z 1) (z' 1)
  · simpa [Analytic.nativeCubeBase] using hscaled (z 2) (z' 2)

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}

/-- **The local core point is Lipschitz in the unsheared base.** -/
theorem localCorePoint_dist_le (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ N)
    (b0 : Fin p.C) {K : ℝ} (hK : 0 ≤ K) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (z z' : Event) :
    ‖packetLocalCorePoint N B p b0 K R c z - packetLocalCorePoint N B p b0 K R c z'‖ ≤
      K ^ R * ((1 + 2 * (p.κ * N ^ (2 * δ₀ * L)) * (1 + ‖p.u b0‖)) *
        ‖unshearedPacketBase p b0 z - unshearedPacketBase p b0 z'‖) := by
  have hκ : 1 ≤ p.κ := hp.1
  have hKR : 0 ≤ K ^ R := pow_nonneg hK R
  unfold packetLocalCorePoint
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hKR]
  apply mul_le_mul_of_nonneg_left _ hKR
  rw [nativeBase_packetNativeCubePoint, nativeBase_packetNativeCubePoint]
  exact (nativeCubeBase_dist_le (by linarith) _ _).trans (hp.native_base_le_unsheared hN b0 z z')

end Path

/-- The ancestor's clock signal is its test over its thickness. -/
theorem clock_ancestorSignal_eq {W : ℕ} (Nk : ℝ) (p : PathData W) (a : Fin p.C) (z : Ev) :
    clockParentSignal p a (ancestorSignal Nk p a) z =
      MvPolynomial.eval (ParentSource.xp z.1 z.2) (p.R a) / ParentSource.δ Nk (p.r (p.lev a)) := by
  rw [← ancestorSignal_clock, one_mul, physicalParentSignal, inv_mul_eq_div]

/-- The literal clock coordinates of the ancestor are its base and its clock signal. -/
theorem clockParentCoordinates_eq_snoc {W : ℕ} (p : PathData W) (a : Fin p.C) (P : Po) (z : Ev) :
    clockParentCoordinates p a P z =
      Fin.snoc (FieldRowLists.baseOf p a z) (clockParentSignal p a P z) := rfl

section Cores

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K : ℝ} {e R : ℕ}

/-- **Height pieces of the ancestor's test at a middle depth.** Inside one kept core entry of a
middle packet `b0` (at a registered depth of the core source, below the ancestor `a`), the
ancestor's clock signal `R_a/δ_a` oscillates by at most the middle thickness ratio `δ_mid/δ_a`
(times `2K⁸`) plus a Lipschitz term in the unsheared base of ANY packet `b`, paid with the clock
ratio `h_b/h_mid`. -/
theorem ancestor_height_pieces (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    {Tt : Type*} {m : ℕ} {H₀ : Fin (d.W k) → Set Event} {u : Tt → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, original w ⊆ d.E k w) (hHbase : ∀ w, original w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K) (hpower : d.N k ^ (τ + ε) ≤ K)
    (hκK : 3 * p.κ ≤ K) {D J : ℕ} (hD : 5186 ≤ D) (hjets : Analytic.DenseJetBound D J)
    (a b : Fin p.C) (j : Fin n) (hr : 0 ≤ p.r (depth j)) (hrL : p.r (depth j) ≤ d.L)
    (b0 : Fin p.C) (hγ0 : p.γ b0 = p.γ a)
    (hwidth : ParentSource.δ (d.N k) (p.r (depth j)) ≤ ParentSource.δ (d.N k) (p.r (p.lev a)))
    (hF0 : p.F b0 ⊆ p.F a)
    (piece : Σ v : (C.values j).ActiveValue, ↥(C.cores j v).codes × Bool)
    (hpiece : piece ∈ FieldRowLists.oldCorePieces C j b0)
    (x y : Event) (hx : x ∈ (C.cores j piece.1).kept piece.2)
    (hy : y ∈ (C.cores j piece.1).kept piece.2) :
    |clockParentSignal p a (ancestorSignal (d.N k) p a) x -
        clockParentSignal p a (ancestorSignal (d.N k) p a) y| ≤
      2 * (K ^ 14 * (K ^ 6)⁻¹ * (ParentSource.δ (d.N k) (p.r (depth j)) / ParentSource.δ (d.N k) (p.r (p.lev a)))) +
        ((K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
          (K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
            ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b0))⁻¹) *
              ‖unshearedPacketBase p b x - unshearedPacketBase p b y‖))) := by
  classical
  rcases piece with ⟨v, ci⟩
  have hv : v.1.1 = b0 := by
    simpa only [FieldRowLists.oldCorePieces, Set.Finite.mem_toFinset, mem_ofPred_eq] using hpiece
  subst hv
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hKpos : 0 < K := by linarith
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1
  have hBworld : ∀ w, 0 < d.B k w := by
    obtain ⟨_, _, _, _, _, _, _, _, hformat, _⟩ := hd
    obtain ⟨M, D, hformat⟩ := hformat
    intro w
    exact ((hformat k).2.2.2.1 w).2.1
  have hlev : p.lev v.1.1 = depth j := v.2.1
  have hwv : ParentSource.δ (d.N k) (p.r (p.lev v.1.1)) ≤ ParentSource.δ (d.N k) (p.r (p.lev a)) := by
    rw [hlev]; exact hwidth
  have hHE' : ∀ w, C.source j w ⊆ d.E k w := fun w => (C.subset j w).trans (hHE w)
  have hHbase' : ∀ w, C.source j w ⊆ Q.base w := fun w => (C.subset j w).trans (hHbase w)
  let Cj := C.cores j v
  have hi : (Cj.kept ci).Nonempty := ⟨x, hx⟩
  let U : Set Event := {x, y}
  have hU : U ⊆ Cj.raw ci := by
    intro z hz
    rcases hz with rfl | hz
    · exact (Cj.subset ci).1 hx
    · rw [mem_singleton_iff] at hz
      subst hz
      exact (Cj.subset ci).1 hy
  let comparison := 1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u v.1.1‖)
  let diam := K ^ R * (comparison *
    ‖unshearedPacketBase p v.1.1 x - unshearedPacketBase p v.1.1 y‖)
  have hdiam : ∀ z ∈ U, ∀ z' ∈ U,
      ‖packetLocalCorePoint (d.N k) (d.B k) p v.1.1 K R (Cj.center ci.1.1) z -
        packetLocalCorePoint (d.N k) (d.B k) p v.1.1 K R (Cj.center ci.1.1) z'‖ ≤ diam := by
    intro z hz z' hz'
    have hpair (z z' : Event) : ‖packetLocalCorePoint (d.N k) (d.B k) p v.1.1 K R
        (Cj.center ci.1.1) z - packetLocalCorePoint (d.N k) (d.B k) p v.1.1 K R
        (Cj.center ci.1.1) z'‖ ≤ K ^ R * (comparison *
          ‖unshearedPacketBase p v.1.1 z - unshearedPacketBase p v.1.1 z'‖) :=
      localCorePoint_dist_le hp hN v.1.1 hKpos.le R _ z z'
    have hdiam0 : 0 ≤ diam := by positivity
    rcases hz with rfl | hz <;> rcases hz' with rfl | hz'
    · simpa using hdiam0
    · rw [mem_singleton_iff] at hz'; subst hz'; exact hpair _ _
    · rw [mem_singleton_iff] at hz; subst hz
      refine (hpair _ _).trans (le_of_eq ?_)
      rw [norm_sub_rev (unshearedPacketBase p v.1.1 _)]
    · rw [mem_singleton_iff] at hz hz'; subst hz hz'; simpa using hdiam0
  have hosc := CoreEntryData.actual_core_signal_oscillation (C.values j) Q hpure hd hp hHE'
    hHbase' hK hmax hpower hκK v.1.1 hlev hr hrL (hBworld _) v.1.2 Cj ci hi hD hjets a hγ0 hwv
    hF0 diam U hU hdiam x (by simp [U]) y (by simp [U])
  -- the diameter in the child's unsheared base
  have hscale := AncestorFrames.scaled_base_distance p v.1.1 b x y
  have h0 : (0 : ℝ) < ((2 : ℝ) ^ p.T (p.lev v.1.1))⁻¹ := by positivity
  have hclock : ‖unshearedPacketBase p v.1.1 x - unshearedPacketBase p v.1.1 y‖ =
      (((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev v.1.1))⁻¹) *
        ‖unshearedPacketBase p b x - unshearedPacketBase p b y‖ := by
    rw [div_mul_eq_mul_div, eq_div_iff h0.ne']
    linear_combination hscale
  have hu : ‖p.u v.1.1‖ ≤ d.K k + 2 * p.κ ^ 2 := original_packet_center_velocity hd hp v.1.1
  have hdiamle : diam ≤ K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) *
      (1 + (d.K k + 2 * p.κ ^ 2))) *
        ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev v.1.1))⁻¹) *
          ‖unshearedPacketBase p b x - unshearedPacketBase p b y‖)) := by
    rw [← hclock]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hKpos.le R)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hN0 : 0 ≤ p.κ * d.N k ^ (2 * δ₀ * d.L) :=
      mul_nonneg hκ (Real.rpow_nonneg (by linarith) _)
    dsimp only [comparison]
    nlinarith
  have hB0 : 0 ≤ (K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹) :=
    mul_nonneg (pow_nonneg (pow_nonneg hKpos.le _) _) (add_nonneg hκ (by positivity))
  have hδ : ParentSource.δ (d.N k) (p.r (p.lev v.1.1)) = ParentSource.δ (d.N k) (p.r (depth j)) := by rw [hlev]
  rw [hδ] at hosc
  rw [clock_ancestorSignal_eq, clock_ancestorSignal_eq]
  exact hosc.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiamle hB0))

/-- **Base-only row lists of the ancestor's test.** Rows Lipschitz in the ancestor's clock
coordinates `(unsheared base of a, R_a/δ_a)` on a reference set `Er` of retained events of the
core source in the child `b` take, in every unsheared base cube of radius `θ` of the child, at
most `(K¹⁰ · 2K^(3R+18)) · 9³` row bins of mesh `pm`. The pieces are the kept core entries of the
middle packet `b0` (an ancestor of `b` at the registered depth `j`); `hsmall` asks that the
cube's diameter in the base of `a` (clock ratio `h_b/h_a`), the middle height error
`2K⁸ δ_mid/δ_a`, the Lipschitz height term (clock ratio `h_b/h_mid`) and `ρ` fit in one mesh. -/
theorem ancestor_row_lists (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    {Tt : Type*} {m : ℕ} {H₀ : Fin (d.W k) → Set Event} {u : Tt → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, original w ⊆ d.E k w) (hHbase : ∀ w, original w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K) (hpower : d.N k ^ (τ + ε) ≤ K)
    (hκK : 3 * p.κ ≤ K) {D J : ℕ} (hD : 5186 ≤ D) (hjets : Analytic.DenseJetBound D J)
    (a b : Fin p.C) (j : Fin n) (hr : 0 ≤ p.r (depth j)) (hrL : p.r (depth j) ≤ d.L)
    (b0 : Fin p.C) (hb0 : p.lev b0 = depth j) (hγ0 : p.γ b0 = p.γ a)
    (hwidth : ParentSource.δ (d.N k) (p.r (depth j)) ≤ ParentSource.δ (d.N k) (p.r (p.lev a)))
    (hF0 : p.F b0 ⊆ p.F a) (hFb : p.F b ⊆ p.F b0)
    (Er : Set Event) (hEr : Er ⊆ C.current (p.γ a) ∩ p.F b)
    {ι : Type*} (st : Event → ι) (Gs : ι → Fin 3 → ℝ)
    {Lp ρ θ pm : ℝ} (hLp : 0 ≤ Lp) (hθ : 0 ≤ θ) (hpm : 0 < pm)
    (hreg : ∀ x ∈ Er, ∀ y ∈ Er, ‖Gs (st x) - Gs (st y)‖ ≤
      Lp * (‖clockParentCoordinates p a (ancestorSignal (d.N k) p a) x -
        clockParentCoordinates p a (ancestorSignal (d.N k) p a) y‖ + ρ))
    (hsmall : Lp * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev a))⁻¹) * (2 * θ) +
        (2 * (K ^ 14 * (K ^ 6)⁻¹ * (ParentSource.δ (d.N k) (p.r (depth j)) /
          ParentSource.δ (d.N k) (p.r (p.lev a)))) +
          ((K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b0))⁻¹) * (6 * θ))))) +
        ρ) ≤ pm) :
    ∀ c' : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ),
      (F.card : ℝ) ≤ (K ^ 10 * (2 * K ^ (3 * R + 18))) * 9 ^ 3 ∧
      ∀ x ∈ Er, (∀ i, |unshearedPacketBase p b x i - c' i| ≤ θ) →
        (fun i => ⌊Gs (st x) i / pm⌋) ∈ F := by
  classical
  intro c'
  have hKpos : 0 < K := by linarith
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  let Eb : Set Event := Er ∩ {x | ∀ i, |unshearedPacketBase p b x i - c' i| ≤ θ}
  let piece : (Σ v : (C.values j).ActiveValue, ↥(C.cores j v).codes × Bool) → Set Event :=
    fun σ' => (C.cores j σ'.1).kept σ'.2
  let height : Event → ℝ := clockParentSignal p a (ancestorSignal (d.N k) p a)
  -- every retained event of the child lies in a kept core entry of the middle packet
  have hcover : ∀ x ∈ Eb, ∃ i ∈ FieldRowLists.oldCorePieces C j b0, x ∈ piece i := by
    intro x hx
    obtain ⟨hxC, hxF⟩ := hEr hx.1
    have hret := C.current_cores j (p.γ a) hxC
    obtain ⟨hres, hU⟩ := hret
    simp only [mem_iUnion] at hU
    obtain ⟨v, hv⟩ := hU
    by_cases hγv : p.γ v.1.1 = p.γ a
    · rw [ite_eq_left hγv] at hv
      obtain ⟨hin, hkept⟩ := hv
      simp only [mem_iUnion] at hkept
      obtain ⟨ci, hci⟩ := hkept
      have hxbase : x ∈ Q.base (p.γ a) :=
        hHbase _ ((C.subset j _) ((C.values j).residual_subset _ hres))
      have hxv : x ∈ p.F v.1.1 :=
        (((C.values j).subset v.1.1 v.1.2).2 (((C.values j).subset v.1.1 v.1.2).1 hin)).2
      have heq : v.1.1 = b0 := Q.base_packet_unique (p.γ a) x hxbase v.1.1 b0
        (v.2.1.trans hb0.symm) hγv hγ0 hxv (hFb hxF)
      refine ⟨⟨v, ci⟩, ?_, hci⟩
      simp only [FieldRowLists.oldCorePieces, Set.Finite.mem_toFinset, mem_ofPred_eq]
      exact heq
    · rw [ite_eq_right hγv] at hv
      exact absurd hv (notMem_empty x)
  -- coordinates of the child cube
  have hcoord : ∀ x ∈ Eb, ∀ y ∈ Eb, ∀ i : Fin 3,
      |unshearedPacketBase p b x i - unshearedPacketBase p b y i| ≤ 2 * θ := by
    intro x hx y hy i
    have h1 := hx.2 i
    have h2 := hy.2 i
    calc |unshearedPacketBase p b x i - unshearedPacketBase p b y i|
        = |(unshearedPacketBase p b x i - c' i) - (unshearedPacketBase p b y i - c' i)| := by
          ring_nf
      _ ≤ |unshearedPacketBase p b x i - c' i| + |unshearedPacketBase p b y i - c' i| :=
          abs_sub _ _
      _ ≤ 2 * θ := by linarith
  have hchild : ∀ x ∈ Eb, ∀ y ∈ Eb,
      ‖unshearedPacketBase p b x - unshearedPacketBase p b y‖ ≤ 6 * θ := by
    intro x hx y hy
    refine (Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _).trans ?_
    rw [Fin.sum_univ_three]
    have h0 := hcoord x hx y hy 0
    have h1 := hcoord x hx y hy 1
    have h2 := hcoord x hx y hy 2
    simp only [PiLp.sub_apply]
    linarith
  -- the cube in the ancestor's base
  have hratio : 0 ≤ ((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev a))⁻¹ := by positivity
  have hbase : ∀ x ∈ Eb, ∀ y ∈ Eb,
      ‖FieldRowLists.baseOf p a x - FieldRowLists.baseOf p a y‖ ≤
        (((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev a))⁻¹) * (2 * θ) := by
    intro x hx y hy
    rw [FieldRowLists.baseOf_sub p a b x y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio]
    apply mul_le_mul_of_nonneg_left _ hratio
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs, Pi.sub_apply]
    exact hcoord x hx y hy i
  -- heights inside one piece
  have hB0 : 0 ≤ (K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹) :=
    mul_nonneg (pow_nonneg (pow_nonneg hKpos.le _) _) (add_nonneg hκ (by positivity))
  have hcomp : 0 ≤ 1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2)) := by
    have hKd : 0 ≤ d.K k := by linarith [hd.2.2.1.1 k]
    have : 0 ≤ p.κ * d.N k ^ (2 * δ₀ * d.L) := mul_nonneg hκ (Real.rpow_nonneg (by linarith) _)
    positivity
  have hratio0 : 0 ≤ ((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b0))⁻¹ := by positivity
  have hheight : ∀ i ∈ FieldRowLists.oldCorePieces C j b0, ∀ x ∈ Eb, x ∈ piece i →
      ∀ y ∈ Eb, y ∈ piece i → |height x - height y| ≤
        (2 * (K ^ 14 * (K ^ 6)⁻¹ * (ParentSource.δ (d.N k) (p.r (depth j)) /
          ParentSource.δ (d.N k) (p.r (p.lev a)))) +
          ((K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b0))⁻¹) * (6 * θ))))) +
          0 * ‖FieldRowLists.baseOf p a x - FieldRowLists.baseOf p a y‖ := by
    intro i hi x hx hxi y hy hyi
    rw [zero_mul, add_zero]
    refine (ancestor_height_pieces C Q hpure hd hp hHE hHbase hK hmax hpower hκK hD hjets a b j
      hr hrL b0 hγ0 hwidth hF0 i hi x y hxi hyi).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hchild x hx y hy) hratio0) hcomp)
      (pow_nonneg hKpos.le R)) hB0)
  -- the rows in the ancestor's clock coordinates
  have hphysical : ∀ x ∈ Eb, ∀ y ∈ Eb, ‖Gs (st x) - Gs (st y)‖ ≤
      Lp * (‖(Fin.snoc (FieldRowLists.baseOf p a x) (height x) : Fin 4 → ℝ) -
        Fin.snoc (FieldRowLists.baseOf p a y) (height y)‖ + ρ) := by
    intro x hx y hy
    rw [← clockParentCoordinates_eq_snoc, ← clockParentCoordinates_eq_snoc]
    exact hreg x hx.1 y hy.1
  have hbaseD : 0 ≤ (((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev a))⁻¹) * (2 * θ) := by
    positivity
  have hheightD : 0 ≤ 2 * (K ^ 14 * (K ^ 6)⁻¹ * (ParentSource.δ (d.N k) (p.r (depth j)) /
          ParentSource.δ (d.N k) (p.r (p.lev a)))) +
          ((K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b0))⁻¹) * (6 * θ)))) := by
    have hδ0 : 0 ≤ ParentSource.δ (d.N k) (p.r (depth j)) /
        ParentSource.δ (d.N k) (p.r (p.lev a)) := by
      unfold ParentSource.δ; positivity
    have h1 : 0 ≤ 2 * (K ^ 14 * (K ^ 6)⁻¹ * (ParentSource.δ (d.N k) (p.r (depth j)) /
        ParentSource.δ (d.N k) (p.r (p.lev a)))) := by positivity
    have h2 : 0 ≤ K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) *
        (1 + (d.K k + 2 * p.κ ^ 2))) *
          ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b0))⁻¹) * (6 * θ))) :=
      mul_nonneg (pow_nonneg hKpos.le R) (mul_nonneg hcomp (by positivity))
    exact add_nonneg h1 (mul_nonneg hB0 h2)
  obtain ⟨F, hF, hFmem⟩ := Qualification.base_row_list_of_height_pieces Eb
    (FieldRowLists.baseOf p a) height (fun x => Gs (st x)) (FieldRowLists.oldCorePieces C j b0)
    piece hbaseD hheightD le_rfl hLp hpm hcover hbase hheight hphysical
    (by simpa only [add_zero, one_mul] using hsmall)
  refine ⟨F, hF.trans ?_, fun x hx hbox => hFmem x ⟨hx, hbox⟩⟩
  exact mul_le_mul_of_nonneg_right (FieldRowLists.oldCorePieces_card_le (C := C) j b0 hKpos.le)
    (by norm_num)

end Cores

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph
