import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

section IsOpenEmbeddingComap

open MeasureTheory Measure

lemma Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (comap φ μ) :=
  .comap' μ hφ.continuous hφ.measurableEmbedding

end IsOpenEmbeddingComap
