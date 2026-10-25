-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.TubePackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.GrainPacket

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- The single-tube statement at fixed error and cutoff parameters. -/
def TubePacketStatement (β τ ε η d₀ : ℝ) : Prop :=
      ∀ δ ρ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ ρ → ρ ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → V) (Z : Fin n → Set V)
        (F : Finset (Fin n)) (y w : V),
        F.Nonempty → ‖w‖ = 1 →
        (∀ i ∈ F, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T (ρ / 2) y w ∧
          MeasurableSet (Z i) ∧ Z i ⊆ T δ (x i) (v i)) →
        (∀ i, i ∉ F → Z i = ∅) → X δ n x v →
        O (δ ^ η * F.card * δ ^ 2) ≤ ∑ i ∈ F, μ (Z i) →
        (∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
          q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
            δ ^ (-η) * (r / ρ) ^ β * q n {i | p ∈ Z i}) →
        4 * δ ^ ε * (ρ / δ) ≤ (F.card : ℝ) ∧
        ∀ c : ℝ, δ ^ (1 - τ) / ρ ≤ c → c ≤ δ ^ ε * (ρ / δ) / F.card →
          ∃ (Z' : Fin n → Set V) (m : ℝ),
            (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i) ∧
            O (δ ^ ε) * ∑ i ∈ F, μ (Z i) ≤ ∑ i ∈ F, μ (Z' i) ∧
            (∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
              q n {i | p ∈ Z' i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
                δ ^ (-ε) * (r / ρ) ^ β * q n {i | p ∈ Z' i}) ∧
            (∀ p, (∃ i, p ∈ Z' i) → q n {i | p ∈ Z' i} ∈ Set.Icc m (2 * m)) ∧
            Nonempty (GrainPacket δ ε ρ c x v Z' y w)

/-- The frozen single-tube theorem, with its geometric output packaged for
subsequent multiplicity refinement and assembly. -/
theorem tube_packets_of (hTG : TubeGrains) {β τ ε : ℝ}
    (hβ : 0 < β) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ 0 < d₀ ∧ TubePacketStatement β τ ε η d₀ := by
  obtain ⟨η, d₀, hη, hd₀, hmain⟩ := hTG β τ ε hβ hτ hε
    O rfl q rfl T rfl X rfl P rfl
  refine ⟨η, d₀, hη, hd₀, ?_⟩
  intro δ ρ hδ hδd hδρ hρ1 n x v Z F y w hF hw hgeom hzero hX hmass hbr
  obtain ⟨hcount, hgrains⟩ := hmain δ ρ hδ hδd hδρ hρ1 n x v Z F y w
    hF hw hgeom hzero hX hmass hbr
  refine ⟨hcount, ?_⟩
  intro c hclo hchi
  obtain ⟨Z', m, L, z, e, G, hZ', hret, hbr', hmult, hgeom', hdisj, hunion, hdense, hcross⟩ :=
    hgrains c hclo hchi
  exact ⟨Z', m, hZ', hret, hbr', hmult, ⟨{
    L := L, center := z, frame := e, shading := G,
    geometry := hgeom', disjoint := hdisj, cover := hunion, density := hdense,
    crossing := hcross }⟩⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
