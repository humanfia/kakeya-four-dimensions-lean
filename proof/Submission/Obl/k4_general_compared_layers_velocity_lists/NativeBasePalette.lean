-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.NativeBasePalette; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.NativeGeometry
import Submission.Lib.K4MovingMeshBoxes.Geometry

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Bounded native signal can be summed out without losing the original
external palette factor. -/
theorem bounded_signal_base_cap_with_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (signal : Ω → ℝ) (condition : Ω → Prop)
    {δ a L C : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (w : ℝ≥0∞) (hwt : w ≠ ⊤)
    (hbound : ∀ᵐ ω ∂μ, condition ω → |signal ω| ≤ L)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {ω | Submission.Lib.K4AffineMeshCaps.baseMesh δ (Z ω) = q ∧
        ⌊signal ω / a⌋ = j ∧ condition ω} ≤ ENNReal.ofReal (C * δ ^ 3) * w)
    (q : Fin 3 → ℤ) :
    μ {ω | Submission.Lib.K4AffineMeshCaps.baseMesh δ (Z ω) = q ∧ condition ω} ≤
      ENNReal.ofReal ((4 * L / a + 2) * C * δ ^ 3) * w := by
  have heq (c : ℝ) (hc : 0 ≤ c) : ENNReal.ofReal (c * w.toReal) = ENNReal.ofReal c * w := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hwt]
  have hc := Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal
    μ Z signal condition hδ ha hL (mul_nonneg hC ENNReal.toReal_nonneg) hbound
    (fun q j => by
      have h := hcap q j
      convert h using 1
      rw [mul_right_comm, heq _ (mul_nonneg hC (by positivity))]) q
  convert hc using 1
  rw [← heq _ (by positivity)]
  congr 1
  ring

/-- Integrate a weighted primitive base cap through a moving box, retaining
its literal external palette factor. -/
theorem moving_box_cap_with_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {δ radius L C : ℝ} (hδ : 0 < δ) (hdr : δ ≤ radius)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, δ ≤ width i)
    (hmove : ∀ i, L * δ ≤ width i)
    (w : ℝ≥0∞) (hwt : w ≠ ⊤)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {ω | Submission.Lib.K4MovingMeshBoxes.baseMesh δ (Z ω) = q ∧ condition ω} ≤
        ENNReal.ofReal (C * δ ^ 3) * w) :
    μ {ω | Z ω ∈ Submission.Lib.K4MovingMeshBoxes.movingBox
      time radius center velocity width ∧ condition ω} ≤
      ENNReal.ofReal (600 * C * radius * width 0 * width 1) * w := by
  have heq (c : ℝ) (hc : 0 ≤ c) : ENNReal.ofReal (c * w.toReal) = ENNReal.ofReal c * w := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hwt]
  have hc := Submission.Lib.K4MovingMeshBoxes.measure_movingBox_of_cell_cap
    μ Z condition hδ hdr hL (mul_nonneg hC ENNReal.toReal_nonneg)
    time center velocity width hv hdw hmove (fun q => by
      convert hcap q using 1
      rw [mul_right_comm, heq _ (mul_nonneg hC (by positivity))])
  have hwidth : ∀ i, 0 ≤ width i := fun i => hδ.le.trans (hdw i)
  have hradius : 0 ≤ radius := hδ.le.trans hdr
  have hw₀ := hwidth 0
  have hw₁ := hwidth 1
  convert hc using 1
  rw [← heq _ (by positivity)]
  congr 1
  ring

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The primitive unit native-signal joint caps imply pure base caps in
each original velocity bin, with only a subpower loss. -/
theorem native_base_cell_palette_cap (hbase : p.Basic) {k : ℕ} {r m : ℝ}
    (hN : 0 < p.N k) (hK : 1 ≤ p.K k)
    (hcap : ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = q ∧
        ⌊MvPolynomial.eval (p.x k ω.1 ω.2) (p.P k)⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-r)) ^ 3) *
            p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀})
    (q : Fin 3 → ℤ) (v₀ : ℤ) :
    p.μ k {ω | p.z k (p.N k) r ω = q ∧
      ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀} ≤
      ENNReal.ofReal (6 * p.K k ^ 2 * (p.N k ^ (-r)) ^ 3) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀} := by
  rcases hbase k with ⟨hb, hν, hπ, hdom, hρ, hunit, hmass, hP, hclip, hnative⟩
  letI := hπ
  have hbound : ∀ᵐ ω ∂p.μ k, |MvPolynomial.eval (p.x k ω.1 ω.2) (p.P k)| ≤ p.K k := by
    have htime : ∀ᵐ ω ∂p.μ k, ω.2 ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      have heq : {ω : α × ℝ | ω.2 ∉ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
        ext ω
        simp
      rw [heq]
      exact hunit
    filter_upwards [htime, hnative] with ω ht hn
    exact (hn.1 ω.2 ht).1
  have hz : (fun ω : α × ℝ => Submission.Lib.K4AffineMeshCaps.baseMesh
      (p.N k ^ (-r)) (p.x k ω.1 ω.2 ∘ Fin.castSucc)) = p.z k (p.N k) r := by
    funext ω j
    fin_cases j <;> rfl
  have hc := bounded_signal_base_cap_with_weight (p.μ k)
    (fun ω => p.x k ω.1 ω.2 ∘ Fin.castSucc)
    (fun ω => MvPolynomial.eval (p.x k ω.1 ω.2) (p.P k))
    (fun ω => ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀)
    (δ := p.N k ^ (-r)) (a := 1) (C := p.K k) (L := p.K k)
    (Real.rpow_pos_of_pos hN _) (by norm_num) (by linarith) (by linarith)
    (p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀}) (measure_ne_top _ _)
    (hbound.mono fun _ h _ => h)
    (fun q a => by
      have heq := congrFun hz
      simp_rw [heq, div_one]
      exact hcap q a v₀) q
  simp_rw [congrFun hz] at hc
  apply hc.trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simp only [div_one]
  nlinarith

/-- A moving original source box has a pure base ceiling in each original
velocity bin. This also handles native comparison bands wider than one. -/
theorem native_source_box_base_cap (hbase : p.Basic)
    {k : ℕ} {r m radius L : ℝ} (hN : 0 < p.N k) (hK : 1 ≤ p.K k)
    (hmesh : p.N k ^ (-r) ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, p.N k ^ (-r) ≤ width i)
    (hmove : ∀ i, L * p.N k ^ (-r) ≤ width i)
    (v₀ : ℤ) (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (E : Set (α × ℝ))
    (hbox : ∀ ω ∈ E,
      ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
        Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width)
    (hvel : ∀ ω ∈ E, ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀)
    (hcap : ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = q ∧
        ⌊MvPolynomial.eval (p.x k ω.1 ω.2) (p.P k)⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-r)) ^ 3) *
            p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'}) :
    σ E ≤ ENNReal.ofReal (3600 * p.K k ^ 2 * radius * width 0 * width 1) *
      p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀} := by
  letI := (hbase k).2.2.1
  have hz (ω : α × ℝ) : Submission.Lib.K4MovingMeshBoxes.baseMesh (p.N k ^ (-r))
      ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] = p.z k (p.N k) r ω := by
    funext i
    fin_cases i <;> rfl
  have hc := moving_box_cap_with_weight (p.μ k)
    (fun ω => ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2])
    (fun ω => ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀)
    (C := 6 * p.K k ^ 2) (Real.rpow_pos_of_pos hN _) hmesh hL (by positivity)
    time center velocity width hv hdw hmove
    (p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀}) (measure_ne_top _ _)
    (by
      intro q
      simp_rw [hz]
      exact native_base_cell_palette_cap p hbase hN hK hcap q v₀)
  calc
    σ E ≤ p.μ k E := hσ E
    _ ≤ p.μ k {ω | ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
        Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀} :=
      measure_mono (fun ω hω => ⟨hbox ω hω, hvel ω hω⟩)
    _ ≤ _ := by convert hc using 1 <;> congr 2 <;> ring

end Parent
end
end Submission.Obl.k4_general_compared_layers_velocity_lists
