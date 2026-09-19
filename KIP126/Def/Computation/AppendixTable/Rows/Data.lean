import KIP126.Def.Computation.AppendixTable.Data

/-!
# Typed Appendix rows

This module is the source-shaped catalogue for the twelve tables printed in
`aimpaper/main.tex`.  Row class expressions are syntax trees, rather than
unparsed TeX: a generator carries its `(stem, filtration, index)` data, named
classes are atoms, and products/sums/cell annotations are explicit nodes.
The catalogue records the paper's row keys and source locations.  It does not
turn a printed differential into a theorem; its status is an input consumed by
later computation and comparison statements.
-/

namespace KIP126.Computation

/-- The version of the Lin computation from which the paper tables were exported. -/
inductive DatasetVersion
  | lwxV126_3Cw49
  deriving DecidableEq, Repr, Inhabited

/-- Cell tags used by the Hopf-cofiber table. -/
inductive Cell
  | bottom
  | top
  deriving DecidableEq, Repr, Inhabited

/-- A class name that is not one of the indexed `x` generators. -/
abbrev ClassName := String

/-- Typed atomic classes.  `named` is a catalogue name (for example `h_0` or
`B_4`), while `generator` records the indices in `x_{n,s}` directly. -/
inductive ClassAtom
  | named (name : ClassName)
  | generator (stem filtration : Nat) (index : Option Nat)
  deriving DecidableEq

/-- Sparse expressions over the named classes and indexed generators. -/
inductive ClassTerm
  | atom (value : ClassAtom)
  | power (value : ClassTerm) (exponent : Nat)
  | product (factors : List ClassTerm)
  | sum (terms : List ClassTerm)
  | cell (which : Cell) (value : ClassTerm)

namespace ClassTerm

mutual
  def validBool : ClassTerm → Bool
    | .atom (.named name) => decide (name ≠ "")
    | .atom (.generator ..) => true
    | .power value _ => validBool value
    | .product values => validListBool values
    | .sum values => validListBool values
    | .cell _ value => validBool value
  def validListBool : List ClassTerm → Bool
    | [] => false
    | value :: values => validBool value && (values.isEmpty || validListBool values)
end

/-- A term contains at least one atom with a nonempty catalogue name. -/
def Valid (term : ClassTerm) : Prop := term.validBool = true

end ClassTerm

/-- The metadata attached to every displayed expression. -/
structure ExpressionMetadata where
  dataset : DatasetVersion
  table : AppendixTableId
  stem : Nat
  filtration : Nat
  internalDegree : Nat
  cell : Option Cell := none


/-- A class expression with its paper bidegree and source table. -/
structure TypedClassExpression where
  metadata : ExpressionMetadata
  term : ClassTerm


namespace TypedClassExpression

/-- Metadata degree is the Adams total degree `t = (t-s)+s`. -/
def DegreeValid (expression : TypedClassExpression) : Prop :=
  expression.metadata.internalDegree =
    expression.metadata.stem + expression.metadata.filtration

/-- The syntax tree is nonempty and its metadata names the table's spectrum. -/
def Valid (expression : TypedClassExpression) : Prop :=
  expression.term.Valid ∧ expression.DegreeValid

end TypedClassExpression

/-- Direction of a differential row in the paper table. -/
inductive DifferentialDirection
  | outgoing
  | incoming
  deriving DecidableEq, Repr, Inhabited

/-- How the paper records a row's status. -/
inductive AppendixRowStatus
  | zeroBand (low high : Nat)
  | permanent
  | differential (direction : DifferentialDirection) (length : Nat)
      (target : Option TypedClassExpression) (possibleTargets : List TypedClassExpression)
  | survivesThrough (page : Nat)


namespace AppendixRowStatus

/-- Whether a status is the incoming presentation of a relation. -/
def isIncoming : AppendixRowStatus → Bool
  | .zeroBand .. => false
  | .permanent => false
  | .differential .incoming .. => true
  | .differential .outgoing .. => false
  | .survivesThrough .. => false

/-- A question mark in the paper is an unresolved target, not a zero target. -/
def unresolved : AppendixRowStatus → Bool
  | .zeroBand .. => false
  | .permanent => false
  | .differential _ _ none _ => true
  | .differential _ _ (some _) _ => false
  | .survivesThrough .. => true

end AppendixRowStatus

/-- A stable key for one differential relation.  The same key can be
attached to outgoing and incoming presentations when a later input joins
the two records; row keys remain independent audit locators. -/
structure DifferentialRelationId where
  value : Nat

namespace DifferentialRelationId

def Valid (relation : DifferentialRelationId) : Prop := relation.value ≠ 0

def validBool (relation : DifferentialRelationId) : Bool := decide (relation.value ≠ 0)

end DifferentialRelationId

/-- A source locator for one printed row. -/
structure AppendixRowLocator where
  file : String := "aimpaper/main.tex"
  line : Nat
  deriving DecidableEq, Repr, Inhabited

/-- One nonempty row in one of the twelve paper tables. -/
structure AppendixRow where
  key : Nat
  table : AppendixTableId
  stem : Nat
  filtration : Nat
  source : TypedClassExpression
  status : AppendixRowStatus
  relation : Option DifferentialRelationId
  locator : AppendixRowLocator


namespace AppendixRow

/-- The row key is unique in the canonical catalogue. -/
def KeyValid (row : AppendixRow) : Prop := row.key ≠ 0

/-- The row's expression metadata agrees with its table and bidegree. -/
def MetadataValid (row : AppendixRow) : Prop :=
  row.source.metadata.table = row.table ∧
  row.source.metadata.stem = row.stem ∧
  row.source.metadata.filtration = row.filtration ∧
  row.source.metadata.internalDegree = row.stem + row.filtration

/-- A row record is a well-formed typed input. -/
def RelationValid (row : AppendixRow) : Prop :=
  match row.relation with
  | none => True
  | some relation => relation.Valid

def Valid (row : AppendixRow) : Prop :=
  row.KeyValid ∧ row.MetadataValid ∧ row.RelationValid

/-- Executable key and metadata check used by catalogue regressions. -/
def validBool (row : AppendixRow) : Bool :=
  decide (row.key ≠ 0) &&
    decide (row.source.metadata.table = row.table) &&
    decide (row.source.metadata.stem = row.stem) &&
    decide (row.source.metadata.filtration = row.filtration) &&
    decide (row.source.metadata.internalDegree = row.stem + row.filtration) &&
    row.source.term.validBool &&
    match row.relation with
    | none => true
    | some relation => relation.validBool

end AppendixRow

/-- A contiguous interval omitted from the paper's display is a certified zero
band in the catalogue.  It carries only a display fact, not a mathematical
claim that an external computation has proved a vanishing theorem. -/
structure AppendixZeroBand where
  table : AppendixTableId
  low : Nat
  high : Nat
  locator : AppendixRowLocator


namespace AppendixZeroBand

def Valid (band : AppendixZeroBand) : Prop := band.low ≤ band.high

def validBool (band : AppendixZeroBand) : Bool := decide (band.low ≤ band.high)

end AppendixZeroBand

/-- Build an expression at an explicit stem and filtration.  The table field
identifies the paper table which supplied the expression; target expressions
can therefore retain their own bidegree while remaining tied to that source. -/
def expressionAt (table : AppendixTableId) (stem filtration : Nat)
    (term : ClassTerm) (cell : Option Cell := none) : TypedClassExpression :=
  { metadata :=
      { dataset := .lwxV126_3Cw49
        table := table
        stem := stem
        filtration := filtration
        internalDegree := stem + filtration
        cell := cell }
    term := term }

/-- Stable helper for building an expression at a source row. -/
def sourceExpression (table : AppendixTableId) (filtration : Nat)
    (term : ClassTerm) (cell : Option Cell := none) : TypedClassExpression :=
  expressionAt table table.stem filtration term cell

/-- Build a class atom while retaining its indexed generator fields. -/
def generator (stem filtration : Nat) (index : Option Nat := none) : ClassTerm :=
  .atom (.generator stem filtration index)

/-- Build a named class atom. -/
def named (name : String) : ClassTerm := .atom (.named name)

/-- Product and sum smart constructors used by the generated catalogue. -/
def product (factors : List ClassTerm) : ClassTerm := .product factors

def sum (terms : List ClassTerm) : ClassTerm := .sum terms

def power (term : ClassTerm) (exponent : Nat) : ClassTerm := .power term exponent

def bottomCell (term : ClassTerm) : ClassTerm := .cell .bottom term

def topCell (term : ClassTerm) : ClassTerm := .cell .top term

end KIP126.Computation
