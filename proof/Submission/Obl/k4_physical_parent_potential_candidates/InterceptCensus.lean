-- Adapted from this LOT tree, o286, branch x1021, commit 128bb7e2,
-- Submission/Obl/k4_native_field_original_candidates/InterceptCensus.lean.
-- Original session x1021. Accepted helper results remain imported.
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

open Set MeasureTheory

namespace Submission.Obl.k4_physical_parent_potential_candidates

/-- The one-dimensional consequence of the accepted integer-code box
estimate, used for literal own-intercept bins. -/
theorem floor_mem_interval_of_close (C : ℕ) {x y w : ℝ} (hw : 0 < w)
    (hxy : |x-y| ≤ (C : ℝ)*w) :
    ⌊x/w⌋ ∈ Finset.Icc (⌊y/w⌋-(C : ℤ)) (⌊y/w⌋+(C : ℤ)) := by
  have h := Submission.Lib.K4ListedExceptions.floor_code_mem_integerCodeBox C
    (fun _ : Fin 1 => x) (fun _ => y) (fun _ => w) (fun _ => hw) (fun _ => hxy)
  have hc := (Submission.Lib.K4ListedExceptions.mem_integerCodeBox C
    (fun _ : Fin 1 => ⌊y/w⌋) (fun _ => ⌊x/w⌋)).mp h
  exact Finset.mem_Icc.mpr (hc 0)

/-- A finite joint catalogue, with at most `2C+1` possible intercept bins
above each joint code, pays for every actually occupied intercept/base pair. -/
theorem finite_pair_catalogue {Ω B H : Type*} [DecidableEq B] [DecidableEq H]
    (S : Set Ω) (joint : Ω → B × H) (group : Ω → ℤ) (C : ℕ)
    (hj : Set.Finite {k | ∃ e ∈ S, joint e = k})
    (hlocal : ∀ e ∈ S, ∀ f ∈ S, joint e = joint f →
      group e ∈ Finset.Icc (group f-(C : ℤ)) (group f+(C : ℤ))) :
    Set.Finite {k : ℤ × B | ∃ e ∈ S, (group e, (joint e).1) = k} ∧
      ({k : ℤ × B | ∃ e ∈ S, (group e, (joint e).1) = k}).ncard ≤
        (2*C+1)*({k | ∃ e ∈ S, joint e = k}).ncard := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    let I := hj.toFinset
    have hex (k : B × H) (hk : k ∈ I) : ∃ e ∈ S, joint e = k := hj.mem_toFinset.mp hk
    let rep (k : B × H) : Ω := if hk : k ∈ I then Classical.choose (hex k hk) else e₀
    have hrep (k : B × H) (hk : k ∈ I) : rep k ∈ S ∧ joint (rep k) = k := by
      simp only [rep, dif_pos hk]
      exact Classical.choose_spec (hex k hk)
    let cover : Finset (ℤ × B) := I.biUnion fun k =>
      (Finset.Icc (group (rep k)-(C : ℤ)) (group (rep k)+(C : ℤ))).image (fun g => (g, k.1))
    have hsub : {k : ℤ × B | ∃ e ∈ S, (group e, (joint e).1) = k} ⊆ (cover : Set (ℤ × B)) := by
      rintro k ⟨e, he, rfl⟩
      have hei : joint e ∈ I := hj.mem_toFinset.mpr ⟨e, he, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨joint e, hei, Finset.mem_image.mpr ⟨group e, ?_, rfl⟩⟩
      exact hlocal e he (rep (joint e)) (hrep (joint e) hei).1 (hrep (joint e) hei).2.symm
    have hfinite := cover.finite_toSet.subset hsub
    refine ⟨hfinite, ?_⟩
    have hcard : cover.card ≤ I.card*(2*C+1) := by
      calc
        _ ≤ ∑ k ∈ I,
            ((Finset.Icc (group (rep k)-(C : ℤ)) (group (rep k)+(C : ℤ))).image
              (fun g => (g, k.1))).card := Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ I, (2*C+1) := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.card_image_le.trans
          rw [Int.card_Icc]
          omega
        _ = _ := by simp
    rw [Set.ncard_eq_toFinset_card _ hfinite, Set.ncard_eq_toFinset_card _ hj]
    have hfsub : hfinite.toFinset ⊆ cover := by
      intro k hk
      exact hsub (hfinite.mem_toFinset.mp hk)
    exact ((Finset.card_le_card hfsub).trans hcard).trans_eq (Nat.mul_comm _ _)
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hS]

/-- Own-intercept fits transfer the original joint census to an actual
intercept/base census. The signal and base meshes retain their original units. -/
theorem intercept_pair_census {Ω : Type*}
    (S : Set Ω) (z : Ω → Fin 3 → ℝ) (X intercept : Ω → ℝ) (P : (Fin 3 → ℝ) → ℝ)
    (p w θ Lip : ℝ) (hp : 0 < p) (hw : 0 < w) (hLip0 : 0 ≤ Lip)
    (hθ : θ ≤ w) (hmesh : Lip*p ≤ w)
    (hfit : ∀ e ∈ S, |X e-P (z e)-intercept e| ≤ θ)
    (hLip : ∀ e ∈ S, ∀ f ∈ S, |P (z e)-P (z f)| ≤ Lip*‖z e-z f‖)
    (hj : Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
      ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}) :
    Set.Finite {k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
      (⌊intercept e/w⌋, (fun i => ⌊z e i/p⌋)) = k} ∧
      ({k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
        (⌊intercept e/w⌋, (fun i => ⌊z e i/p⌋)) = k}).ncard ≤
          9*({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
            ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard := by
  apply finite_pair_catalogue S (fun e => ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋))
    (fun e => ⌊intercept e/w⌋) 4 hj
  intro e he f hf hcode
  have hheight : |X e-X f| ≤ w :=
    Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell hw (congrArg Prod.snd hcode)
  have hbase : ‖z e-z f‖ ≤ p := by
    apply (pi_norm_le_iff_of_nonneg hp.le).mpr
    intro i
    exact Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell hp
      (congrArg (fun k : (Fin 3 → ℤ) × ℤ => k.1 i) hcode)
  have hpol : |P (z e)-P (z f)| ≤ w :=
    (hLip e he f hf).trans ((mul_le_mul_of_nonneg_left hbase hLip0).trans hmesh)
  have hclose : |intercept e-intercept f| ≤ (4 : ℝ)*w := by
    obtain ⟨he₁, he₂⟩ := abs_le.mp (hfit e he)
    obtain ⟨hf₁, hf₂⟩ := abs_le.mp (hfit f hf)
    obtain ⟨hh₁, hh₂⟩ := abs_le.mp hheight
    obtain ⟨hp₁, hp₂⟩ := abs_le.mp hpol
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact floor_mem_interval_of_close 4 hw hclose

end Submission.Obl.k4_physical_parent_potential_candidates
