import FormalConjectures.Util.ProblemImports

/-!
Minimal example exercising `instance` holes in the multi-hole
eval-problem pipeline. The carrier type is itself a hole so the source
has no non-hole declarations and the generator does not need a
`ChallengeDeps` split.
-/

@[category research solved, AMS 0]
def WidgetCarrier : Type := sorry

@[category research solved, AMS 0]
instance instInhabitedWidget : Inhabited WidgetCarrier := sorry
