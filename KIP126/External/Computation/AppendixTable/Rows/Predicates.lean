import KIP126.External.Computation.AppendixTable.Rows.Data

/-! Well-formedness predicates for the external table transcription. -/

namespace KIP126.Computation

namespace ClassTerm

/-- A term contains at least one atom with a nonempty catalogue name. -/
def Valid (term : ClassTerm) : Prop := term.validBool = true

end ClassTerm

namespace TypedClassExpression

/-- Metadata degree is the Adams total degree `t = (t-s)+s`. -/
def DegreeValid (expression : TypedClassExpression) : Prop :=
  expression.metadata.internalDegree =
    expression.metadata.stem + expression.metadata.filtration

/-- The syntax tree is nonempty and its metadata names the table's spectrum. -/
def Valid (expression : TypedClassExpression) : Prop :=
  expression.term.Valid ∧ expression.DegreeValid

end TypedClassExpression

namespace DifferentialRelationId

def Valid (relation : DifferentialRelationId) : Prop := relation.value ≠ 0

end DifferentialRelationId

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

end AppendixRow

namespace AppendixZeroBand

def Valid (band : AppendixZeroBand) : Prop := band.low ≤ band.high

end AppendixZeroBand

end KIP126.Computation
