/-! Minimal stable-homotopy operations used by the current Adams slice. -/
namespace KIP126.Classical.Adams

/-- The stable-homotopy operations used by the domain layer.  No homotopy
groups or multiplication are assumed here. -/
structure StableHomotopyContext where
  Spectrum : Type
  sphere : Spectrum
  smash : Spectrum → Spectrum → Spectrum

end KIP126.Classical.Adams
