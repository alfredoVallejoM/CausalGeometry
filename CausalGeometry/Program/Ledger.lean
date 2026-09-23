import CausalGeometry.Program.Campaign

namespace CausalGeometry.Program

/-- Number of atomic obligations assigned to each gate. -/
def Campaign.rows : Campaign → Nat
  | .ca00 => 12
  | .ca01 => 14
  | .ca02 => 16
  | .ca03 => 18
  | .ca04 => 14
  | .ca05 => 18
  | .ca06 => 18
  | .ca07 => 16
  | .ca08 => 18
  | .ca09 => 24
  | .ca10 => 18
  | .ca11 => 22
  | .ca12 => 20
  | .ca13 => 24
  | .ca14 => 16
  | .ca15 => 12
  | .ca16 => 20
  | .ca17 => 24
  | .ca18 => 32
  | .ca19 => 32
  | .ca20 => 40

def originalCoreRows : Nat := 186
def eciaRows : Nat := 82
def closureRows : Nat := 12
def wilderberRows : Nat := 20
def originalRows : Nat := 300

def correlativeRestrictionRows : Nat := 24
def derivedArithmeticRows : Nat := 32
def realizationSynthesisRows : Nat := 32
def grandProgramRows : Nat := 40
def extensionRows : Nat := 128

def totalRows : Nat := 428

example : originalCoreRows + eciaRows + closureRows + wilderberRows = originalRows := by
  decide

example :
    correlativeRestrictionRows + derivedArithmeticRows +
      realizationSynthesisRows + grandProgramRows = extensionRows := by
  decide

example : originalRows + extensionRows = totalRows := by
  decide

end CausalGeometry.Program
