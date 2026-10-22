import QEC.Coding.BitTuring.UnaryFieldProjection
import QEC.Coding.ExpanderCodes.LPSEncodedChecks

/-!
# Faithful complete sparse-check bit encoding

Each entry stores coefficient then physical index. A row begins with its entry count;
the whole word begins with its row count. Physical row storage is reversed because the
actual collector prepends rows; the strict decoder restores original check order.
Zeros, duplicates and empty rows are preserved. Truncated/padded fields and out-of-range
typed indices are rejected. This module also proves exact finite product/sum enumeration
needed to match the existing numeric source order. No execution or runtime is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
abbrev Row:=List (ℕ×ℕ)
def entryFields (r:Row):List ℕ:=r.flatMap (fun e=>[e.2,e.1])
def rowFields (rs:List Row):List ℕ:=rs.flatMap (fun r=>r.length::entryFields r)
def decodeEntries:ℕ→List ℕ→Option (Row×List ℕ)
 | 0,xs=>some ([],xs)
 | n+1,k::p::xs=>(decodeEntries n xs).map (fun rs=>((p,k)::rs.1,rs.2))
 | _+1,_=>none
def decodeRows:ℕ→List ℕ→Option (List Row×List ℕ)
 | 0,xs=>some ([],xs)
 | n+1,k::xs=>(decodeEntries k xs).bind (fun r=>(decodeRows n r.2).map (fun rs=>(r.1::rs.1,rs.2)))
 | _+1,[]=>none
def fields (rs:List Row):List ℕ:=rs.length::rowFields rs.reverse
def decodeFields:List ℕ→Option (List Row)
 | []=>none
 | n::xs=>(decodeRows n xs).bind (fun rs=>if rs.2=[] then some rs.1.reverse else none)
def encode (rs:List Row):List Bool:=stream (fields rs)
theorem decodeEntries_entryFields (r:Row) (tail:List ℕ):
 decodeEntries r.length (entryFields r++tail)=some (r,tail):=by
 induction r with
 | nil=>rfl
 | cons e r ih=>
  rcases e with ⟨p,k⟩
  simp only [entryFields] at ih
  simp only [List.length_cons,entryFields,List.flatMap_cons,List.cons_append,List.nil_append,decodeEntries,ih]
  rfl
theorem decodeRows_rowFields (rs:List Row) (tail:List ℕ):
 decodeRows rs.length (rowFields rs++tail)=some (rs,tail):=by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>
  simp only [rowFields] at ih
  simp only [List.length_cons,rowFields,List.flatMap_cons,List.cons_append,List.append_assoc,decodeRows,
   decodeEntries_entryFields,Option.bind_some,ih]
  rfl
theorem decode_encodeFields (rs:List Row):decodeFields (fields rs)=some rs:=by
 have h:=decodeRows_rowFields rs.reverse []
 simp only [List.length_reverse,List.append_nil] at h
 simp only [fields,decodeFields,h,Option.bind_some,List.reverse_reverse]
 rfl
theorem fields_injective:Function.Injective fields:=by
 intro rs ss h
 have he:=congrArg decodeFields h
 rw [decode_encodeFields,decode_encodeFields] at he
 exact Option.some.inj he
theorem encode_injective:Function.Injective encode:=by
 intro rs ss h
 exact fields_injective (stream_injective h)
theorem entryFields_length (r:Row):(entryFields r).length=2*r.length:=by
 induction r with
 | nil=>rfl
 | cons e r ih=>simp only [entryFields,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *;omega
theorem rowFields_length (rs:List Row):(rowFields rs).length=rs.length+2*(rs.map List.length).sum:=by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>
  simp only [rowFields,List.flatMap_cons,List.length_append,List.length_cons,entryFields_length,List.map_cons,List.sum_cons] at *
  omega
theorem entryFields_sum (r:Row):(entryFields r).sum=(r.map fun e=>e.1+e.2).sum:=by
 induction r with
 | nil=>rfl
 | cons e r ih=>simp only [entryFields,List.flatMap_cons,List.sum_append,List.sum_cons,List.sum_nil,List.map_cons] at *;omega
-- Explicit controls retain both zero-valued fields, duplicates and empty row boundaries.
example:decodeFields (fields [[],[(0,0),(0,0)],[]])=some [[],[(0,0),(0,0)],[]]:=by decide
example:fields [[],[(0,0)],[]]≠fields [[(0,0)],[],[]]:=by decide
example:decodeFields [1,2,0,0]=none:=by decide
example:decodeFields [1,0,0]=none:=by decide
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
theorem entryFields_injective:Function.Injective entryFields:=by
 intro r s h
 have hl:=congrArg List.length h
 rw [entryFields_length,entryFields_length] at hl
 have hn:r.length=s.length:=by omega
 have he:=congrArg (fun xs=>decodeEntries r.length (xs++[])) h
 rw [decodeEntries_entryFields,hn,decodeEntries_entryFields] at he
 exact congrArg Prod.fst (Option.some.inj he)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
theorem ofFn_product {α:Type*} {m n:ℕ} (f:Fin m×Fin n→α):
 (List.ofFn fun i:Fin (m*n)=>f (finProdFinEquiv.symm i))=
 (List.ofFn fun i:Fin m=>List.ofFn fun j:Fin n=>f (i,j)).flatten:=by
 rw [List.ofFn_mul]
 apply congrArg List.flatten
 apply congrArg List.ofFn
 funext i
 apply congrArg List.ofFn
 funext j
 have hv: (⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩:Fin (m*n))=finProdFinEquiv (i,j):=by
  apply Fin.ext
  change i.val*n+j.val=j.val+n*i.val
  simp only [Nat.mul_comm,Nat.add_comm]
 rw [hv,Equiv.symm_apply_apply]
theorem ofFn_sum {α:Type*} {m n:ℕ} (f:Fin m⊕Fin n→α):
 (List.ofFn fun i:Fin (m+n)=>f (finSumFinEquiv.symm i))=
 (List.ofFn fun i:Fin m=>f (Sum.inl i))++(List.ofFn fun i:Fin n=>f (Sum.inr i)):=by
 rw [List.ofFn_add]
 simp only [finSumFinEquiv_symm_apply_natAdd]
 congr 1
 apply congrArg List.ofFn
 funext i
 have hv:i.castLE (Nat.le_add_right m n)=Fin.castAdd n i:=by apply Fin.ext;rfl
 rw [hv,finSumFinEquiv_symm_apply_castAdd]
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
theorem ofFn_product_equiv {α A B:Type*} {m n:ℕ} (ea:A≃Fin m) (eb:B≃Fin n) (f:A×B→α):
 (List.ofFn fun i:Fin (m*n)=>f (((Equiv.prodCongr ea eb).trans finProdFinEquiv).symm i))=
 (List.ofFn fun i:Fin m=>List.ofFn fun j:Fin n=>f (ea.symm i,eb.symm j)).flatten:=by
 have h:=ofFn_product (fun x:Fin m×Fin n=>f (ea.symm x.1,eb.symm x.2))
 exact h
theorem ofFn_sum_equiv {α A B:Type*} {m n:ℕ} (ea:A≃Fin m) (eb:B≃Fin n) (f:A⊕B→α):
 (List.ofFn fun i:Fin (m+n)=>f (((Equiv.sumCongr ea eb).trans finSumFinEquiv).symm i))=
 (List.ofFn fun i:Fin m=>f (Sum.inl (ea.symm i)))++(List.ofFn fun i:Fin n=>f (Sum.inr (eb.symm i))):=by
 have h:=ofFn_sum (fun x:Fin m⊕Fin n=>f ((Equiv.sumCongr ea eb).symm x))
 exact h
theorem ofFn_triple {α:Type*} {m n k:ℕ} (f:Fin m×Fin n×Fin k→α):
 (List.ofFn fun i:Fin (m*(n*k))=>f ((lpsSparseTripleEquiv m n k).symm i))=
 (List.ofFn fun i:Fin m=>(List.ofFn fun j:Fin n=>List.ofFn fun t:Fin k=>f (i,j,t)).flatten).flatten:=by
 rw [lpsSparseTripleEquiv,ofFn_product_equiv]
 simp only [Equiv.refl_symm,Equiv.refl_apply]
 apply congrArg List.flatten
 apply congrArg List.ofFn
 funext i
 exact ofFn_product (fun x:Fin n×Fin k=>f (i,x))
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection
def parseFields:ℕ→List Bool→Option (List ℕ)
 | n,[]=>if n=0 then some [] else none
 | n,true::xs=>parseFields (n+1) xs
 | n,false::xs=>(parseFields 0 xs).map (n::·)
theorem parseFields_unary (n a:ℕ) (w:List Bool):
 parseFields n (unary a++false::w)=(parseFields 0 w).map ((n+a)::·):=by
 induction a generalizing n with
 | zero=>simp only [unary,List.replicate_zero,List.nil_append,parseFields,Nat.add_zero]
 | succ a ih=>
  rw [unary_succ,List.cons_append]
  change parseFields (n+1) (unary a++false::w)=_
  rw [ih]
  simp only [Nat.add_assoc,Nat.add_comm 1 a]
theorem parseFields_stream (xs:List ℕ):parseFields 0 (stream xs)=some xs:=by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>
  simp only [stream,parseFields_unary,Nat.zero_add,ih,Option.map_some]
def decode (w:List Bool):Option (List Row):=(parseFields 0 w).bind decodeFields
theorem decode_encode (rs:List Row):decode (encode rs)=some rs:=by
 rw [decode,encode,parseFields_stream,Option.bind_some,decode_encodeFields]
def typedEntry (n s:ℕ) (e:ℕ×ℕ):Option (Fin n×Fin s):=
 if hp:e.1 < n then if hk:e.2 < s then some (⟨e.1,hp⟩,⟨e.2,hk⟩) else none else none
def typedRow (n s:ℕ):Row→Option (List (Fin n×Fin s))
 | []=>some []
 | e::es=>(typedEntry n s e).bind (fun e'=>(typedRow n s es).map (e'::·))
def typedRows (n s:ℕ):List Row→Option (List (List (Fin n×Fin s)))
 | []=>some []
 | r::rs=>(typedRow n s r).bind (fun r'=>(typedRows n s rs).map (r'::·))
def numeric (n s:ℕ) (rs:List (List (Fin n×Fin s))):List Row:=
 rs.map (fun r=>r.map (fun e=>(e.1.val,e.2.val)))
theorem typedEntry_vals {n s:ℕ} (e:Fin n×Fin s):typedEntry n s (e.1.val,e.2.val)=some e:=by
 simp only [typedEntry,e.1.isLt,e.2.isLt,dif_pos]
theorem typedRow_vals {n s:ℕ} (r:List (Fin n×Fin s)):
 typedRow n s (r.map (fun e=>(e.1.val,e.2.val)))=some r:=by
 induction r with
 | nil=>rfl
 | cons e r ih=>simp only [List.map_cons,typedRow,typedEntry_vals,Option.bind_some,ih,Option.map_some]
theorem typedRows_numeric {n s:ℕ} (rs:List (List (Fin n×Fin s))):typedRows n s (numeric n s rs)=some rs:=by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp only [numeric,List.map_cons,typedRows,typedRow_vals,Option.bind_some] at *;rw [ih];rfl
def decodeTyped (n s:ℕ) (w:List Bool):Option (List (List (Fin n×Fin s))):=
 (decode w).bind (typedRows n s)
theorem decodeTyped_encode {n s:ℕ} (rs:List (List (Fin n×Fin s))):
 decodeTyped n s (encode (numeric n s rs))=some rs:=by
 rw [decodeTyped,decode_encode,Option.bind_some,typedRows_numeric]
example:decode [true]=none:=by decide +kernel
example:decode (encode [[],[(0,0),(0,0)],[(7,4)]])=some [[],[(0,0),(0,0)],[(7,4)]]:=by decide +kernel
example:decodeTyped 1 1 (encode [[(1,0)]])=none:=by decide +kernel
example:decodeTyped 1 1 (encode [[(0,1)]])=none:=by decide +kernel
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
def rowsOrEmpty (n s:ℕ) (w:List Bool):List (List (Fin n×Fin s)):=
 (decodeTyped n s w).getD []
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
