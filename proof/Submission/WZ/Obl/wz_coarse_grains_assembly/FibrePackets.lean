-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.FibrePackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.TubePackets
import Submission.WZ.Obl.wz_coarse_grains_assembly.FibreShadings

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- Applying the single-tube theorem to one supported cover fibre. Its
retention bound is expressed as a full sum over the original fine indices. -/
theorem cover_fibre_packet {ω ζ τ e η d₀ δ θ ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hTG : TubePacketStatement (ω * ζ / 100) τ e η d₀)
    (hδ : 0 < δ) (hδd : δ ≤ d₀) (hδρ : δ ≤ 2 * ρ) (hρ1 : 2 * ρ ≤ 1)
    (hgeom : ∀ i, ‖v i‖ = 1 ∧ Y i ⊆ T δ (x i) (v i)) (hX : X δ n x v)
    (hC : C δ θ n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ η (2 * ρ) n N v S Z f)
    (k : Fin N) (hF : (S.filter (fun i => f i = k)).Nonempty)
    (hden : O (δ ^ η * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
      ∑ i ∈ S.filter (fun i => f i = k), μ (Z i)) :
    4 * δ ^ e * (2 * ρ / δ) ≤ ((S.filter (fun i => f i = k)).card : ℝ) ∧
      ∀ c : ℝ, δ ^ (1 - τ) / (2 * ρ) ≤ c →
        c ≤ δ ^ e * (2 * ρ / δ) / (S.filter (fun i => f i = k)).card →
      ∃ (W : Fin n → Set V) (m : ℝ),
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
        (∀ i p, p ∈ W i → i ∈ S ∧ f i = k) ∧
        O (δ ^ e) * (∑ i ∈ S.filter (fun i => f i = k), μ (Z i)) ≤ ∑ i, μ (W i) ∧
        (∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ 2 * ρ →
          q n {i | p ∈ W i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
            δ ^ (-e) * (r / (2 * ρ)) ^ (ω * ζ / 100) * q n {i | p ∈ W i}) ∧
        (∀ p, (∃ i, p ∈ W i) → q n {i | p ∈ W i} ∈ Set.Icc m (2 * m)) ∧
        Nonempty (GrainPacket δ e (2 * ρ) c x v W (y k) (w k)) := by
  classical
  let F := S.filter (fun i => f i = k)
  let Zk := fibreShading S f Z k
  have hinput : ∀ i ∈ F, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T ((2 * ρ) / 2) (y k) (w k) ∧
      MeasurableSet (Zk i) ∧ Zk i ⊆ T δ (x i) (v i) := by
    intro i hi
    obtain ⟨hiS, hfi⟩ := Finset.mem_filter.mp hi
    refine ⟨(hgeom i).1, ?_, fibreShading_measurable S f Z (fun i => (hC.1 i).1) k i,
      (fibreShading_subset S f Z k i).trans ((hC.1 i).2.1.trans (hgeom i).2)⟩
    rw [show (2 * ρ) / 2 = ρ by ring, ← hfi]
    exact hC.2.2.2.1 i hiS
  obtain ⟨hcount, hpack⟩ := hTG δ (2 * ρ) hδ hδd hδρ hρ1 n x v Zk F (y k) (w k)
    hF (hC.2.2.1 k) hinput (fibreShading_zero S f Z k) hX
    (by rw [sum_fibreShading_on_fibre]; exact hden)
    (by
      intro p u r hu hdr hrρ
      simpa only [Zk, mem_fibreShading, and_assoc] using hbr k p u r hu hdr hrρ)
  refine ⟨hcount, ?_⟩
  intro c hclo hchi
  obtain ⟨W, m, hW, hret, hWbr, hmult, hgrain⟩ := hpack c hclo hchi
  have hsupport : ∀ i p, p ∈ W i → i ∈ S ∧ f i = k := by
    intro i p hp
    have hh := (mem_fibreShading S f Z k i p).mp ((hW i).2 hp)
    exact ⟨hh.1, hh.2.1⟩
  refine ⟨W, m, fun i => ⟨(hW i).1, (hW i).2.trans (fibreShading_subset S f Z k i)⟩,
    hsupport, ?_, hWbr, hmult, hgrain⟩
  rw [sum_fibreShading_on_fibre, sum_supported_fibre S f W k hsupport] at hret
  exact hret

end WangZahlLot.Obl.wz_coarse_grains_assembly
