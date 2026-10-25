/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.KernelDomination
import Submission.Lib.K4PolynomialNorming.NormingCoordinates
import Submission.Lib.K4PolynomialNorming.TimeIncrementCoordinates

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

theorem initialObservedLaw {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (μ : Measure Ω) [SFinite μ] (ν : Measure V) :
    μ.map (fun x => (x,fun i : Fin 0 => Fin.elim0 i)) =
      μ.prod (Measure.pi (fun _ : Fin 0 => ν)) := by
  rw [Measure.pi_of_empty (fun _ : Fin 0 => ν) (fun i => Fin.elim0 i), Measure.prod_dirac]

theorem initialObservedLaw_le {H Ω V : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω] [MeasurableSpace V]
    (θ : Measure H) (g : H → Ω) (hg : Measurable g)
    (μ : Measure Ω) [SFinite μ] (ν : Measure V) (hθ : θ.map g ≤ μ) :
    θ.map (fun h => (g h,fun i : Fin 0 => Fin.elim0 i)) ≤
      μ.prod (Measure.pi (fun _ : Fin 0 => ν)) := by
  let v : Fin 0 → V := fun i => Fin.elim0 i
  have hm : Measurable (fun x : Ω => (x,v)) := measurable_id.prodMk measurable_const
  have h := Measure.map_mono hθ hm
  rw [Measure.map_map hm hg,initialObservedLaw μ ν] at h
  exact h

/-- Append one observed coordinate without carrying unobserved latent state. -/
noncomputable def appendObservedCoordinate {Ω V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] (n : ℕ) :
    ((Ω × (Fin n → V)) × V) ≃ᵐ (Ω × (Fin (n+1) → V)) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω)
      (MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => V) (Fin.last n)).symm))

theorem appendObservedCoordinate_measurePreserving {Ω V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V]
    (μ : Measure Ω) [SFinite μ] (ν : Measure V) [SigmaFinite ν] (n : ℕ) :
    MeasurePreserving (appendObservedCoordinate (Ω := Ω) (V := V) n)
      ((μ.prod (Measure.pi (fun _ : Fin n => ν))).prod ν)
      (μ.prod (Measure.pi (fun _ : Fin (n+1) => ν))) := by
  have hs := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => V) (Fin.last n))
  have hswap := Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin n => ν)) (ν := ν)
  have hp := (MeasurePreserving.id μ).prod (hs.comp hswap)
  exact hp.comp (measurePreserving_prodAssoc μ (Measure.pi (fun _ : Fin n => ν)) ν)

/-- Observed histories of a retained process obey the product reference
bound after any finite number of steps. Conditional ceilings concern the
full actual latent past, and no retained measure is normalized. -/
theorem observed_process_history_domination {H Y : ℕ → Type*} {Ω V : Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (Y n)]
    [MeasurableSpace Ω] [MeasurableSpace V]
    (θ : (n : ℕ) → Measure (H n)) [∀ n, SFinite (θ n)]
    (κ : (n : ℕ) → Kernel (H n) (Y n)) [∀ n, IsSFiniteKernel (κ n)]
    (f : (n : ℕ) → H n × Y n → H (n+1)) (hf : ∀ n, Measurable (f n))
    (g : (n : ℕ) → H n → Ω × (Fin n → V)) (hg : ∀ n, Measurable (g n))
    (obs : (n : ℕ) → H n × Y n → V) (hobs : ∀ n, Measurable (obs n))
    (hlaw : ∀ n, θ (n+1) = (θ n ⊗ₘ κ n).map (f n))
    (hcompat : ∀ n z, g (n+1) (f n z) = appendObservedCoordinate n (g n z.1,obs n z))
    (μ : Measure Ω) [SFinite μ] (ν : Measure V) [SigmaFinite ν] (K : ENNReal)
    (hzero : (θ 0).map (g 0) ≤ μ.prod (Measure.pi (fun _ : Fin 0 => ν)))
    (hstep : ∀ n, ∀ᵐ h ∂θ n, (κ n h).map (fun y => obs n (h,y)) ≤ K • ν) :
    ∀ n, (θ n).map (g n) ≤ K^n • (μ.prod (Measure.pi (fun _ : Fin n => ν))) := by
  intro n
  induction n with
  | zero => simpa only [pow_zero, one_smul] using hzero
  | succ n ih =>
    have hdom := history_observed_compProd_le_smul_prod (θ n)
      (μ.prod (Measure.pi (fun _ : Fin n => ν))) ν (κ n) (g n) (obs n)
      (hg n) (hobs n) (K^n) K ih (hstep n)
    have hm : Measurable (fun z : H n × Y n => (g n z.1,obs n z)) :=
      ((hg n).comp measurable_fst).prodMk (hobs n)
    have heq : (θ (n+1)).map (g (n+1)) =
        ((θ n ⊗ₘ κ n).map (fun z : H n × Y n => (g n z.1,obs n z))).map
          (appendObservedCoordinate n) := by
      rw [hlaw n, Measure.map_map (hg (n+1)) (hf n),
        Measure.map_map (appendObservedCoordinate n).measurable hm]
      congr 1
      funext z
      exact hcompat n z
    have hb := Measure.map_mono hdom (appendObservedCoordinate n).measurable
    rw [← heq, Measure.map_smul _ (appendObservedCoordinate n).measurable.aemeasurable,
      (appendObservedCoordinate_measurePreserving μ ν n).map_eq, ← pow_succ] at hb
    exact hb

/-- Separate control labels and endpoint times into the row and fiber
variables of an endpoint-volume bound. -/
noncomputable def separateObservedCoordinates {Ω C T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace T] (n : ℕ) :
    (Ω × (Fin n → C × T)) ≃ᵐ ((Ω × (Fin n → C)) × (Fin n → T)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω)
    (MeasurableEquiv.arrowProdEquivProdArrow C T (Fin n))).trans MeasurableEquiv.prodAssoc.symm

theorem separateObservedCoordinates_measurePreserving {Ω C T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace T]
    (μ : Measure Ω) [SFinite μ] (π : Measure C) [SigmaFinite π]
    (τ : Measure T) [SigmaFinite τ] (n : ℕ) :
    MeasurePreserving (separateObservedCoordinates (Ω := Ω) (C := C) (T := T) n)
      (μ.prod (Measure.pi (fun _ : Fin n => π.prod τ)))
      ((μ.prod (Measure.pi (fun _ : Fin n => π))).prod (Measure.pi (fun _ : Fin n => τ))) := by
  have hsplit := measurePreserving_arrowProdEquivProdArrow C T (Fin n)
    (fun _ => π) (fun _ => τ)
  have hp := (MeasurePreserving.id μ).prod hsplit
  have ha := (measurePreserving_prodAssoc μ (Measure.pi (fun _ : Fin n => π))
    (Measure.pi (fun _ : Fin n => τ))).symm MeasurableEquiv.prodAssoc
  exact ha.comp hp

theorem separateObservedCoordinates_domination {Ω C T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace T]
    (μ : Measure Ω) [SFinite μ] (π : Measure C) [SigmaFinite π]
    (τ : Measure T) [SigmaFinite τ] (n : ℕ)
    (P : Measure (Ω × (Fin n → C × T))) (B : ENNReal)
    (hP : P ≤ B • μ.prod (Measure.pi (fun _ : Fin n => π.prod τ))) :
    P.map (separateObservedCoordinates n) ≤
      B • ((μ.prod (Measure.pi (fun _ : Fin n => π))).prod (Measure.pi (fun _ : Fin n => τ))) := by
  have h := Measure.map_mono hP (separateObservedCoordinates n).measurable
  rw [Measure.map_smul _ (separateObservedCoordinates n).measurable.aemeasurable,
    (separateObservedCoordinates_measurePreserving μ π τ n).map_eq] at h
  exact h

noncomputable def startDependentSignedDurations {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (start : Ω → ℝ) : (Ω × (Fin n → ℝ)) → (Ω × (Fin n → ℝ)) :=
  fun z => (z.1,consecutiveTimeIncrements (start z.1) z.2)

theorem startDependentSignedDurations_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (n : ℕ) (start : Ω → ℝ) (hstart : Measurable start) :
    MeasurePreserving (startDependentSignedDurations n start)
      (μ.prod (volume : Measure (Fin n → ℝ))) (μ.prod volume) := by
  have hc : Measurable (fun z : Ω × (Fin n → ℝ) =>
      (Fin.cons (start z.1) z.2 : Fin (n+1) → ℝ)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero, Function.comp_def] using hstart.comp
        (measurable_fst : Measurable (fun z : Ω × (Fin n → ℝ) => z.1))
    · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
        (measurable_snd : Measurable (fun z : Ω × (Fin n → ℝ) => z.2))
  have hm : Measurable (fun z : Ω × (Fin n → ℝ) =>
      consecutiveTimeIncrements (start z.1) z.2) := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun z : Ω × (Fin n → ℝ) =>
      (Fin.cons (start z.1) z.2 : Fin (n+1) → ℝ) i.succ -
        (Fin.cons (start z.1) z.2 : Fin (n+1) → ℝ) i.castSucc)
    exact ((measurable_pi_apply i.succ).comp hc).sub ((measurable_pi_apply i.castSucc).comp hc)
  exact (MeasurePreserving.id μ).skew_product
    (g := fun (ω : Ω) (t : Fin n → ℝ) => consecutiveTimeIncrements (start ω) t) hm
    (Filter.Eventually.of_forall (fun ω =>
      (consecutiveTimeIncrements_measurePreserving n (start ω)).map_eq))

noncomputable def signedDurationEndpointCoordinates {Ω : Type*} [MeasurableSpace Ω]
    (start : Ω → ℝ) : (Ω × (Fin 6 → ℝ)) → (Ω × ((Fin 5 → ℝ) × ℝ)) :=
  fun z => (z.1,splitHeadCoordinates 5 (consecutiveTimeIncrements (start z.1) z.2))

/-- Start-dependent time differences and the final duration split carry
the same product reference, with no Jacobian loss. -/
theorem signedDurationEndpointCoordinates_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (start : Ω → ℝ) (hstart : Measurable start) :
    MeasurePreserving (signedDurationEndpointCoordinates start)
      (μ.prod (volume : Measure (Fin 6 → ℝ)))
      (μ.prod (volume : Measure ((Fin 5 → ℝ) × ℝ))) := by
  have hs := startDependentSignedDurations_measurePreserving μ 6 start hstart
  have hh := (MeasurePreserving.id μ).prod (splitHeadCoordinates_measurePreserving 5)
  exact hh.comp hs

theorem signedDurationEndpointCoordinates_domination {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (start : Ω → ℝ) (hstart : Measurable start)
    (P : Measure (Ω × (Fin 6 → ℝ))) (B : ENNReal)
    (hP : P ≤ B • μ.prod (volume : Measure (Fin 6 → ℝ))) :
    P.map (signedDurationEndpointCoordinates start) ≤
      B • μ.prod (volume : Measure ((Fin 5 → ℝ) × ℝ)) := by
  have hp := signedDurationEndpointCoordinates_measurePreserving μ start hstart
  have h := Measure.map_mono hP hp.measurable
  rw [Measure.map_smul _ hp.measurable.aemeasurable,hp.map_eq] at h
  exact h

/-- Convert a product ceiling for six observed control/time pairs into
the exact row-by-duration law used by the physical endpoint theorem. -/
theorem sixControlEndpointLaw_domination {Ω C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) [SFinite μ] (π : Measure C) [SigmaFinite π]
    (P : Measure (Ω × (Fin 6 → C × ℝ))) (B : ENNReal)
    (hP : P ≤ B • μ.prod (Measure.pi (fun _ : Fin 6 => π.prod (volume : Measure ℝ))))
    (start : Ω × (Fin 6 → C) → ℝ) (hstart : Measurable start) :
    P.map (fun z => signedDurationEndpointCoordinates start (separateObservedCoordinates 6 z)) ≤
      B • ((μ.prod (Measure.pi (fun _ : Fin 6 => π))).prod
        (volume : Measure ((Fin 5 → ℝ) × ℝ))) := by
  have hs := separateObservedCoordinates_domination μ π (volume : Measure ℝ) 6 P B hP
  have h := signedDurationEndpointCoordinates_domination
    (μ.prod (Measure.pi (fun _ : Fin 6 => π))) start hstart
    (P.map (separateObservedCoordinates 6)) B hs
  have hm := (signedDurationEndpointCoordinates_measurePreserving
    (μ.prod (Measure.pi (fun _ : Fin 6 => π))) start hstart).measurable
  rw [Measure.map_map hm (separateObservedCoordinates 6).measurable] at h
  exact h

end Submission.Lib.K4PolynomialNorming

