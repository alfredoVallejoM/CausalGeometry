namespace CausalGeometry.Program

/-- Frozen campaign gates.

CA16 is the Wilderber generalized restriction bridge.
CA17--CA20 extend the causal arithmetic source theory and its realization
synthesis without replacing earlier campaigns.

CA21--CA25 are the second closure wave:
* CA21: graded causal differential/Hodge/tensor/variational geometry;
* CA22: noncommutative localization and general local arithmetic closure;
* CA23: real ECIA consumption and conservativity/loss accounting;
* CA24: advanced arithmetic/geometric realizations;
* CA25: analytic/spectral operator layer.

These later gates extend the program; they do not retroactively redefine the
meaning of CA00--CA20. -/
inductive Campaign
  | ca00 | ca01 | ca02 | ca03 | ca04 | ca05 | ca06 | ca07 | ca08
  | ca09 | ca10 | ca11 | ca12 | ca13 | ca14 | ca15 | ca16
  | ca17 | ca18 | ca19 | ca20
  | ca21 | ca22 | ca23 | ca24 | ca25
  deriving DecidableEq, Repr, Inhabited

def Campaign.rank : Campaign → Nat
  | .ca00 => 0 | .ca01 => 1 | .ca02 => 2 | .ca03 => 3 | .ca04 => 4
  | .ca05 => 5 | .ca06 => 6 | .ca07 => 7 | .ca08 => 8 | .ca09 => 9
  | .ca10 => 10 | .ca11 => 11 | .ca12 => 12 | .ca13 => 13
  | .ca14 => 14 | .ca15 => 15 | .ca16 => 16 | .ca17 => 17
  | .ca18 => 18 | .ca19 => 19 | .ca20 => 20
  | .ca21 => 21 | .ca22 => 22 | .ca23 => 23 | .ca24 => 24
  | .ca25 => 25

end CausalGeometry.Program
