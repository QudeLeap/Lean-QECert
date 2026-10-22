import QEC.Coding.ExpanderCodes.LPSSparseEmitterBlockMachine
import QEC.Coding.ExpanderCodes.LPSSparseEmitterCodec

/-!
# Exact source semantics of the complete sparse-CSS emitter

The four entry blocks retain the original group-product orientations and the general-field
negative h' coefficient. Every scalar is included. Proved finite product/sum enumeration
shows the complete decoded output is exactly lpsEncodedCheckOutput, with X before Z,
local coordinates before group index, and scalar last. The strict typed bit decoder
recovers the existing original Fin-indexed rows. All runtime certificates are derived
from the actual q-only program, not supplied semantic-output hypotheses.

Source: panteleev-kalachev-2021-good/main.tex:231-238,248-273,589-620,1744.
The arbitrary code field is independent of the graph prime. These are internal execution
and semantics proofs; the unconditional strong centered-theta bound remains unproved.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open LPSSparseEmitterRow
open scoped MatrixGroups
theorem face_number {q D r r':ℕ} [Fact q.Prime] (ac br:Fin D) (i:LPSSparseGroupIndex q):
 (lpsSparseQubitNumbering (r:=r) (r':=r') (Sum.inl (ac,br,i))).val=
 (ac.val*D+br.val)*(lpsPSLList q).length+i.val:=by
 simp [lpsSparseQubitNumbering,lpsSparseTripleEquiv,finProdFinEquiv,finSumFinEquiv]
 ring
theorem vertex_number {q D r r':ℕ} [Fact q.Prime] (ar:Fin (2*r)) (bc:Fin (2*r')) (i:LPSSparseGroupIndex q):
 (lpsSparseQubitNumbering (D:=D) (Sum.inr (ar,bc,i))).val=
 (D*D+ar.val*(2*r')+bc.val)*(lpsPSLList q).length+i.val:=by
 simp [lpsSparseQubitNumbering,lpsSparseTripleEquiv,finProdFinEquiv,finSumFinEquiv]
 ring
def xSpecs {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s))
 (h':Matrix (Fin r') (Fin D) (Fin s)) (ar:Fin (2*r)) (br:Fin D) (scalar:Fin s):List (EntrySpec D):=
 (List.ofFn fun ac:Fin D=>
  {side:=(finProdFinEquiv.symm ar).1,direction:=ac,inverse:=true,right:=true,offset:=ac.val*D+br.val,
   coefficient:=(encodedFieldMul t scalar (h (finProdFinEquiv.symm ar).2 ac)).val})++
 (List.ofFn fun bc:Fin (2*r')=>
  {side:=(finProdFinEquiv.symm bc).1,direction:=br,inverse:=false,right:=false,offset:=D*D+ar.val*(2*r')+bc.val,
   coefficient:=(encodedFieldMul t scalar (encodedFieldNeg t (h' (finProdFinEquiv.symm bc).2 br))).val})
def zSpecs {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s))
 (h':Matrix (Fin r') (Fin D) (Fin s)) (ac:Fin D) (bc:Fin (2*r')) (scalar:Fin s):List (EntrySpec D):=
 (List.ofFn fun br:Fin D=>
  {side:=(finProdFinEquiv.symm bc).1,direction:=br,inverse:=true,right:=false,offset:=ac.val*D+br.val,
   coefficient:=(encodedFieldMul t scalar (h' (finProdFinEquiv.symm bc).2 br)).val})++
 (List.ofFn fun ar:Fin (2*r)=>
  {side:=(finProdFinEquiv.symm ar).1,direction:=ac,inverse:=false,right:=true,offset:=D*D+ar.val*(2*r')+bc.val,
   coefficient:=(encodedFieldMul t scalar (h (finProdFinEquiv.symm ar).2 ac)).val})
def numericRow {q D r r' s:ℕ} [Fact q.Prime] (rs:List (LPSSparseQubitIndex q D r r'×Fin s)):
 LPSSparseEmitterCodec.Row:=rs.map (fun e=>((lpsSparseQubitNumbering e.1).val,e.2.val))
theorem xSpecs_length {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s))
 (h':Matrix (Fin r') (Fin D) (Fin s)) (ar:Fin (2*r)) (br:Fin D) (scalar:Fin s):
 (xSpecs t h h' ar br scalar).length=D+2*r':=by simp [xSpecs]
theorem zSpecs_length {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s))
 (h':Matrix (Fin r') (Fin D) (Fin s)) (ac:Fin D) (bc:Fin (2*r')) (scalar:Fin s):
 (zSpecs t h h' ac bc scalar).length=D+2*r:=by simp [zSpecs]
theorem xSource {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s))
 (ar:Fin (2*r)) (br:Fin D) (scalar:Fin s) (i:LPSSparseGroupIndex a.q):
 entries a g (xSpecs t h h' ar br scalar) (lpsPSLList a.q).length i=
 LPSSparseEmitterCodec.entryFields (numericRow (lpsEncodedCheckRow t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h'
  (Sum.inl ((ar,br,i),scalar)))):=by
 simp only [entries,xSpecs,List.flatMap_def,entry,LPSSparseEmitterAction.product,
  LPSSparseEmitterAction.transformed,LPSSparseEmitterAction.voltage,
  LPSSparseEmitterCodec.entryFields,numericRow,lpsEncodedCheckRow,encodedSparseScalarRow,lpsEncodedXRow,
  List.map_append,List.map_ofFn,Function.comp_def,face_number,vertex_number]
 rfl
theorem zSource {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s))
 (ac:Fin D) (bc:Fin (2*r')) (scalar:Fin s) (i:LPSSparseGroupIndex a.q):
 entries a g (zSpecs t h h' ac bc scalar) (lpsPSLList a.q).length i=
 LPSSparseEmitterCodec.entryFields (numericRow (lpsEncodedCheckRow t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h'
  (Sum.inr ((ac,bc,i),scalar)))):=by
 simp only [entries,zSpecs,List.flatMap_def,entry,LPSSparseEmitterAction.product,
  LPSSparseEmitterAction.transformed,LPSSparseEmitterAction.voltage,
  LPSSparseEmitterCodec.entryFields,numericRow,lpsEncodedCheckRow,encodedSparseScalarRow,lpsEncodedZRow,
  List.map_append,List.map_ofFn,Function.comp_def,face_number,vertex_number]
 rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSemantics
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
def row {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (i:LPSSparseGroupIndex a.q):LPSSparseEmitterCodec.Row:=
 es.map (fun e=>(e.offset*(lpsPSLList a.q).length+
  (LPSSparseEmitterAction.product e.inverse e.right (LPSSparseEmitterAction.voltage a g e.side e.direction) i).val,e.coefficient))
def body (rs:List LPSSparseEmitterCodec.Row):List Bool:=stream (LPSSparseEmitterCodec.rowFields rs)
theorem body_append (rs ss:List LPSSparseEmitterCodec.Row):body (rs++ss)=body rs++body ss:=by
 rw [body,LPSSparseEmitterCodec.rowFields,List.flatMap_append,MatrixListQuery.stream_append]
 rfl
theorem body_flatten (rs:List (List LPSSparseEmitterCodec.Row)):body rs.flatten=(rs.map body).flatten:=by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp only [List.flatten_cons,body_append,ih,List.map_cons]
theorem body_reverse_flatten (rs:List (List LPSSparseEmitterCodec.Row)):
 body rs.flatten.reverse=(rs.reverse.map (fun r=>body r.reverse)).flatten:=by
 rw [List.reverse_flatten,body_flatten]
 simp only [List.map_reverse,List.map_map,Function.comp_def]
theorem row_fields {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (i:LPSSparseGroupIndex a.q):
 LPSSparseEmitterCodec.entryFields (row a g es i)=entries a g es (lpsPSLList a.q).length i:=by
 simp only [LPSSparseEmitterCodec.entryFields,row,List.flatMap_map,entries,entry]
theorem row_length {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (i:LPSSparseGroupIndex a.q):
 (row a g es i).length=es.length:=by simp only [row,List.length_map]
theorem rowWord_eq_body {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (i:LPSSparseGroupIndex a.q):
 LPSSparseEmitterBlock.rowWord a g es (lpsPSLList a.q).length i=body [row a g es i]:=by
 simp only [body,LPSSparseEmitterCodec.rowFields,List.flatMap_cons,List.flatMap_nil,List.append_nil,row_fields,row_length,
  LPSSparseEmitterBlock.rowWord]
theorem words_eq_body {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))) (i:LPSSparseGroupIndex a.q):
 LPSSparseEmitterBlock.words a g rs (lpsPSLList a.q).length i=body (rs.map (fun es=>row a g es i)).reverse:=by
 induction rs with
 | nil=>rfl
 | cons es rs ih=>
  simp only [LPSSparseEmitterBlock.words,ih,rowWord_eq_body,List.map_cons,List.reverse_cons,body_append]
def blockRows {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):List LPSSparseEmitterCodec.Row:=
 (List.ofFn fun i:LPSSparseGroupIndex a.q=>rs.map (fun es=>row a g es i)).flatten
theorem blockWords_eq_body {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):
 LPSSparseEmitterBlock.blockWords a g rs=body (blockRows a g rs).reverse:=by
 simp only [LPSSparseEmitterBlock.blockWords,words_eq_body,blockRows,body_reverse_flatten,List.map_reverse,List.map_ofFn,Function.comp_def]
def rows {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):List LPSSparseEmitterCodec.Row:=
 bs.flatMap (blockRows a g)
theorem words_eq_body_rows {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 LPSSparseEmitterChain.words a g bs=body (rows a g bs).reverse:=by
 induction bs with
 | nil=>rfl
 | cons b bs ih=>simp only [LPSSparseEmitterChain.words,ih,blockWords_eq_body,rows,List.flatMap_cons,List.reverse_append,body_append]
theorem blockRows_length {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):
 (blockRows a g rs).length=(lpsPSLList a.q).length*rs.length:=by
 simp only [blockRows,List.length_flatten,List.map_ofFn,Function.comp_def,List.length_map,List.ofFn_const,List.sum_replicate,Nat.nsmul_eq_mul]
theorem rows_length {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 (rows a g bs).length=LPSSparseEmitterMachine.rowFactor bs*(lpsPSLList a.q).length:=by
 induction bs with
 | nil=>simp [rows,LPSSparseEmitterMachine.rowFactor]
 | cons b bs ih=>
  simp only [rows,List.flatMap_cons,List.length_append,blockRows_length,LPSSparseEmitterMachine.rowFactor,List.map_cons,List.sum_cons] at *
  rw [ih]
  ring
theorem output_eq_encode {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 LPSSparseEmitterMachine.output a g bs=LPSSparseEmitterCodec.encode (rows a g bs):=by
 rw [LPSSparseEmitterMachine.output,words_eq_body_rows,LPSSparseEmitterCodec.encode,LPSSparseEmitterCodec.fields,rows_length]
 rw [body,←MatrixListQuery.stream_append]
 rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSemantics

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open LPSSparseEmitterRow
open scoped MatrixGroups
theorem xRow {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s))
 (ar:Fin (2*r)) (br:Fin D) (scalar:Fin s) (i:LPSSparseGroupIndex a.q):
 LPSSparseEmitterSemantics.row a g (xSpecs t h h' ar br scalar) i=
 numericRow (lpsEncodedCheckRow t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h' (Sum.inl ((ar,br,i),scalar))):=by
 apply LPSSparseEmitterCodec.entryFields_injective
 rw [LPSSparseEmitterSemantics.row_fields]
 exact xSource a g t h h' ar br scalar i
theorem zRow {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s))
 (ac:Fin D) (bc:Fin (2*r')) (scalar:Fin s) (i:LPSSparseGroupIndex a.q):
 LPSSparseEmitterSemantics.row a g (zSpecs t h h' ac bc scalar) i=
 numericRow (lpsEncodedCheckRow t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h' (Sum.inr ((ac,bc,i),scalar))):=by
 apply LPSSparseEmitterCodec.entryFields_injective
 rw [LPSSparseEmitterSemantics.row_fields]
 exact zSource a g t h h' ac bc scalar i
def xBlocks {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 List (List (List (EntrySpec D))):=
 (List.ofFn fun ar:Fin (2*r)=>List.ofFn fun br:Fin D=>List.ofFn fun scalar:Fin s=>xSpecs t h h' ar br scalar).flatten
def zBlocks {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 List (List (List (EntrySpec D))):=
 (List.ofFn fun ac:Fin D=>List.ofFn fun bc:Fin (2*r')=>List.ofFn fun scalar:Fin s=>zSpecs t h h' ac bc scalar).flatten
def blocks {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=xBlocks t h h'++zBlocks t h h'
def check {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)) (c:LPSEncodedCheckIndex a.q D r r' s):LPSSparseEmitterCodec.Row:=
 numericRow (lpsEncodedCheckRow t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h' c)
def checks {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 List LPSSparseEmitterCodec.Row:=
 (lpsEncodedCheckOutput t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h').map
  (fun rs=>rs.map (fun e=>(e.1.val,e.2.val)))
theorem checks_ofFn {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 checks a g t h h'=List.ofFn (fun i=>check a g t h h' (lpsEncodedCheckNumbering.symm i)):=by
 simp only [checks,lpsEncodedCheckOutput,List.map_ofFn,List.map_map,check,numericRow,Function.comp_def]
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open LPSSparseEmitterRow LPSSparseEmitterFiniteOrder
open scoped MatrixGroups
def xChecks {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 List LPSSparseEmitterCodec.Row:=
 (List.ofFn fun ar:Fin (2*r)=>(List.ofFn fun br:Fin D=>
  (List.ofFn fun i:LPSSparseGroupIndex a.q=>List.ofFn fun scalar:Fin s=>check a g t h h' (Sum.inl ((ar,br,i),scalar))).flatten).flatten).flatten
def zChecks {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 List LPSSparseEmitterCodec.Row:=
 (List.ofFn fun ac:Fin D=>(List.ofFn fun bc:Fin (2*r')=>
  (List.ofFn fun i:LPSSparseGroupIndex a.q=>List.ofFn fun scalar:Fin s=>check a g t h h' (Sum.inr ((ac,bc,i),scalar))).flatten).flatten).flatten
theorem checks_split {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 checks a g t h h'=xChecks a g t h h'++zChecks a g t h h':=by
 rw [checks_ofFn,lpsEncodedCheckNumbering,ofFn_sum_equiv]
 have hx:=ofFn_product_equiv (lpsSparseTripleEquiv (2*r) D (lpsPSLList a.q).length) (Equiv.refl (Fin s))
  (fun c=>check a g t h h' (Sum.inl c))
 have hz:=ofFn_product_equiv (lpsSparseTripleEquiv D (2*r') (lpsPSLList a.q).length) (Equiv.refl (Fin s))
  (fun c=>check a g t h h' (Sum.inr c))
 rw [hx,hz]
 simp only [Equiv.refl_symm,Equiv.refl_apply]
 have hxt:=ofFn_triple (fun c:Fin (2*r)×Fin D×LPSSparseGroupIndex a.q=>
  List.ofFn fun j:Fin s=>check a g t h h' (Sum.inl (c,j)))
 have hzt:=ofFn_triple (fun c:Fin D×Fin (2*r')×LPSSparseGroupIndex a.q=>
  List.ofFn fun j:Fin s=>check a g t h h' (Sum.inr (c,j)))
 rw [hxt,hzt]
 simp only [List.flatten_flatten,List.map_ofFn,Function.comp_def]
 rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open LPSSparseEmitterRow
open scoped MatrixGroups
theorem xRows {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterSemantics.rows a g (xBlocks t h h')=xChecks a g t h h':=by
 simp only [LPSSparseEmitterSemantics.rows,xBlocks,List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def,
  LPSSparseEmitterSemantics.blockRows,xRow,check,List.flatten_flatten,xChecks]
theorem zRows {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterSemantics.rows a g (zBlocks t h h')=zChecks a g t h h':=by
 simp only [LPSSparseEmitterSemantics.rows,zBlocks,List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def,
  LPSSparseEmitterSemantics.blockRows,zRow,check,List.flatten_flatten,zChecks]
theorem rows_eq_checks {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterSemantics.rows a g (blocks t h h')=checks a g t h h':=by
 rw [blocks,LPSSparseEmitterSemantics.rows,List.flatMap_append]
 rw [←LPSSparseEmitterSemantics.rows,←LPSSparseEmitterSemantics.rows,xRows,zRows,checks_split]
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
open LPSSparseEmitterRow
def machine {p D r r' s:ℕ} (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 LPSSparseEmitterMachine.machine g (blocks t h h')
noncomputable def time {p D r r' s:ℕ} (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 LPSSparseEmitterMachine.time g (blocks t h h')
def output {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 LPSSparseEmitterCodec.encode (checks a g t h h')
theorem output_eq {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterMachine.output a g (blocks t h h')=output a g t h h':=by
 rw [LPSSparseEmitterSemantics.output_eq_encode,rows_eq_checks]
 rfl
noncomputable def exec {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 EvalsToInTime (TM2.step (machine g t h h').program) ((machine g t h h').init (unary a.q))
 (some ((machine g t h h').halt (output a g t h h'))) ((time g t h h').eval (unary a.q).length):=by
 have hx:=LPSSparseEmitterMachine.exec a g (blocks t h h')
 rw [output_eq] at hx
 exact hx
noncomputable def outputsInTime {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 TM2OutputsInTime (machine g t h h').toFinTM2 (unary a.q) (some (output a g t h h')) ((time g t h h').eval (unary a.q).length):=
 Machine.outputsInTime _ _ _ _ (exec a g t h h')
noncomputable def blockExec {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 EvalsToInTime (TM2.step (machine g t h h').program) ((machine g t h h').init (unary a.q))
 (some ((machine g t h h').halt (output a g t h h')))
 ((time g t h h').eval (2*Fintype.card PSL(2,ZMod a.q))):=by
 have hx:=exec a g t h h'
 refine {hx with steps_le_m:=hx.steps_le_m.trans ?_}
 exact Composition.polynomial_eval_monotone _ (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
theorem decode_output {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeFields (LPSSparseEmitterCodec.fields (checks a g t h h'))=some (checks a g t h h'):=
 LPSSparseEmitterCodec.decode_encodeFields _
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open scoped MatrixGroups
theorem decodeTyped_output {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeTyped
 (D*(D*(lpsPSLList a.q).length)+(2*r)*((2*r')*(lpsPSLList a.q).length)) s (output a g t h h')=
 some (lpsEncodedCheckOutput t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h'):=
 LPSSparseEmitterCodec.decodeTyped_encode _
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing
open scoped MatrixGroups
noncomputable def computableInPolyTime {p D r r' s:ℕ} (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a g t h h') where
 tm:=(machine g t h h').toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time g t h h'
 outputsFun:=fun a=>by
  change TM2OutputsInTime (machine g t h h').toFinTM2 (List.map id (unary a.q))
   (some (List.map id (output a g t h h'))) ((time g t h h').eval (unary a.q).length)
  have hx:=outputsInTime a g t h h'
  dsimp only [Machine.toFinTM2] at hx ⊢
  simpa only [List.map_id] using hx
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
