;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(set-option :timeout 10000)

(declare-datatypes (
      (StructuralSpecialTypeInfo 0)
    ) (
    ( (StructuralSpecialTypeInfo@cons (StructuralSpecialTypeInfo$PODType Bool) (StructuralSpecialTypeInfo$APIType Bool) (StructuralSpecialTypeInfo$Parsable Bool)) )
))

(declare-datatypes (
      (bsq_safestring 0)
      (bsq_stringof 0)
      (bsq_uuid 0)
      (bsq_logicaltime 0)
      (bsq_cryptohash 0)
      (bsq_enum 0)
      (bsq_idkeysimple 0)
      (bsq_idkeycompound 0)
      (BKeyValue 0)
    ) (
    ( (bsq_safestring@cons (bsq_safestring_type Int) (bsq_safestring_value String)) )
    ( (bsq_stringof@cons (bsq_stringof_type Int) (bsq_stringof_value String)) )
    ( (bsq_uuid@cons (bsq_uuid_value String)) )
    ( (bsq_logicaltime@cons (bsq_logicaltime_value Int)) )
    ( (bsq_cryptohash@cons (bsq_cryptohash_value String)) )
    ( (bsq_enum@cons (bsq_enum_type Int) (bsq_enum_value Int)) )
    ( (bsq_idkeysimple@cons (bsq_idkeysimple_type Int) (bsq_idkeysimple_value BKeyValue)) )
    ( (bsq_idkeycompound@cons (bsq_idkeycompound_type Int) (bsq_idkeycompound_value (Array Int BKeyValue))) )
    (
      (bsqkey_none) 
      (bsqkey_bool (bsqkey_bool_value Bool))
      (bsqkey_int (bsqkey_int_value Int))
      (bsqkey_bigint (bsqkey_bigint_value Int))
      (bsqkey_string (bsqkey_string_value String))
      (bsqkey_safestring (bsqkey_safestring_value bsq_safestring))
      (bsqkey_stringof (bsqkey_stringof_value bsq_stringof))
      (bsqkey_uuid (bsqkey_uuid_value bsq_uuid))
      (bsqkey_logicaltime (bsqkey_logicaltime_value bsq_logicaltime))
      (bsqkey_cryptohash (bsqkey_cryptohash_value bsq_cryptohash))
      (bsqkey_enum (bsqkey_enum_value bsq_enum))
      (bsqkey_idkeysimple (bsqkey_idkeysimple_value bsq_idkeysimple))
      (bsqkey_idkeycompound (bsqkey_idkeycompound_value bsq_idkeycompound))
    )
))

(declare-datatypes ( 
    (bsq_buffer 0)
    (bsq_bufferof 0)
    (bsq_bytebuffer 0)
    (bsq_isotime 0)
    (bsq_regex 0)
    (bsq_tuple 0)
    (bsq_record 0)
    (nscore__list_t_nscore__int_I10I 0)
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_buffer@cons (bsq_buffer_type Int) (bsq_buffer_contents String)) )
    ( (bsq_bufferof@cons (bsq_bufferof_type Int) (bsq_bufferof_contents String)) )
    ( (bsq_bytebuffer@cons (bsq_bytebuffer_contents (Seq Int))) )
    ( (bsq_isotime@cons (bsq_isotime_value Int)) )
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ( (bsq_tuple@cons (bsq_tuple_concepts StructuralSpecialTypeInfo) (bsq_tuple_entries (Array Int BTerm)))  )
    ( (bsq_record@cons (bsq_record_concepts StructuralSpecialTypeInfo) (bsq_record_entries (Array String BTerm))) )
    ( (nscore__list_t_nscore__int_I10I@cons (nscore__list_t_nscore__int_I10I@@size Int) (nscore__list_t_nscore__int_I10I@@entries (Array Int Int))) )
    (
      (bsq_object@empty)
    (cons@bsq_object_from_nscore__list_t_nscore__int_I10I (bsqterm_object_nscore__list_t_nscore__int_I10I_value nscore__list_t_nscore__int_I10I))
    )
    (
      (bsqterm@clear)
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_float64 (bsqterm_float64_value (_ FloatingPoint 11 53)))
      (bsqterm_buffer (bsqterm_buffer_value bsq_buffer))
      (bsqterm_bufferof (bsqterm_bufferof_value bsq_bufferof))
      (bsqterm_bytebuffer (bsqterm_bytebuffer_value bsq_bytebuffer))
      (bsqterm_isotime (bsqterm_isotime_value bsq_isotime))
      (bsqterm_regex (bsqterm_regex_value bsq_regex))
      (bsqterm_tuple (bsqterm_tuple_value bsq_tuple))
      (bsqterm_record (bsqterm_record_value bsq_record))
      (bsqterm_object (bsqterm_object_type Int) (bsqterm_object_value bsq_object))
    )
))

(declare-const MIRNominalTypeEnum_nscore__bigintI0I Int)
(assert (= MIRNominalTypeEnum_nscore__bigintI0I 1))
(declare-const MIRNominalTypeEnum_nscore__boolI1I Int)
(assert (= MIRNominalTypeEnum_nscore__boolI1I 3))
(declare-const MIRNominalTypeEnum_nscore__buffercompressionI2I Int)
(assert (= MIRNominalTypeEnum_nscore__buffercompressionI2I 5))
(declare-const MIRNominalTypeEnum_nscore__bufferencodingI3I Int)
(assert (= MIRNominalTypeEnum_nscore__bufferencodingI3I 7))
(declare-const MIRNominalTypeEnum_nscore__bufferformatI4I Int)
(assert (= MIRNominalTypeEnum_nscore__bufferformatI4I 9))
(declare-const MIRNominalTypeEnum_nscore__bytebufferI5I Int)
(assert (= MIRNominalTypeEnum_nscore__bytebufferI5I 11))
(declare-const MIRNominalTypeEnum_nscore__cryptohashI6I Int)
(assert (= MIRNominalTypeEnum_nscore__cryptohashI6I 13))
(declare-const MIRNominalTypeEnum_nscore__float64I7I Int)
(assert (= MIRNominalTypeEnum_nscore__float64I7I 15))
(declare-const MIRNominalTypeEnum_nscore__intI8I Int)
(assert (= MIRNominalTypeEnum_nscore__intI8I 17))
(declare-const MIRNominalTypeEnum_nscore__isotimeI9I Int)
(assert (= MIRNominalTypeEnum_nscore__isotimeI9I 19))
(declare-const MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I Int)
(assert (= MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I 21))
(declare-const MIRNominalTypeEnum_nscore__logicaltimeI12I Int)
(assert (= MIRNominalTypeEnum_nscore__logicaltimeI12I 23))
(declare-const MIRNominalTypeEnum_nscore__noneI13I Int)
(assert (= MIRNominalTypeEnum_nscore__noneI13I 25))
(declare-const MIRNominalTypeEnum_nscore__regexI14I Int)
(assert (= MIRNominalTypeEnum_nscore__regexI14I 27))
(declare-const MIRNominalTypeEnum_nscore__stringI15I Int)
(assert (= MIRNominalTypeEnum_nscore__stringI15I 29))
(declare-const MIRNominalTypeEnum_nscore__uuidI16I Int)
(assert (= MIRNominalTypeEnum_nscore__uuidI16I 31))
(declare-const MIRNominalTypeEnum_nscore__anyI17I Int)
(assert (= MIRNominalTypeEnum_nscore__anyI17I 33))
(declare-const MIRNominalTypeEnum_nscore__apitypeI18I Int)
(assert (= MIRNominalTypeEnum_nscore__apitypeI18I 35))
(declare-const MIRNominalTypeEnum_nscore__apivalueI19I Int)
(assert (= MIRNominalTypeEnum_nscore__apivalueI19I 37))
(declare-const MIRNominalTypeEnum_nscore__convertableI20I Int)
(assert (= MIRNominalTypeEnum_nscore__convertableI20I 39))
(declare-const MIRNominalTypeEnum_nscore__enumI21I Int)
(assert (= MIRNominalTypeEnum_nscore__enumI21I 41))
(declare-const MIRNominalTypeEnum_nscore__expandoable_t_nscore__int_I22I Int)
(assert (= MIRNominalTypeEnum_nscore__expandoable_t_nscore__int_I22I 43))
(declare-const MIRNominalTypeEnum_nscore__idkeyI23I Int)
(assert (= MIRNominalTypeEnum_nscore__idkeyI23I 45))
(declare-const MIRNominalTypeEnum_nscore__keytypeI24I Int)
(assert (= MIRNominalTypeEnum_nscore__keytypeI24I 47))
(declare-const MIRNominalTypeEnum_nscore__objectI25I Int)
(assert (= MIRNominalTypeEnum_nscore__objectI25I 49))
(declare-const MIRNominalTypeEnum_nscore__parsableI26I Int)
(assert (= MIRNominalTypeEnum_nscore__parsableI26I 51))
(declare-const MIRNominalTypeEnum_nscore__podtypeI27I Int)
(assert (= MIRNominalTypeEnum_nscore__podtypeI27I 53))
(declare-const MIRNominalTypeEnum_nscore__recordI28I Int)
(assert (= MIRNominalTypeEnum_nscore__recordI28I 55))
(declare-const MIRNominalTypeEnum_nscore__someI29I Int)
(assert (= MIRNominalTypeEnum_nscore__someI29I 57))
(declare-const MIRNominalTypeEnum_nscore__truthyI30I Int)
(assert (= MIRNominalTypeEnum_nscore__truthyI30I 59))
(declare-const MIRNominalTypeEnum_nscore__tupleI31I Int)
(assert (= MIRNominalTypeEnum_nscore__tupleI31I 61))
(declare-const MIRNominalTypeEnum_nscore__validatorI32I Int)
(assert (= MIRNominalTypeEnum_nscore__validatorI32I 63))

(declare-const MIRNominalTypeEnum_None Int)
(declare-const MIRNominalTypeEnum_Bool Int)
(declare-const MIRNominalTypeEnum_Int Int)
(declare-const MIRNominalTypeEnum_BigInt Int)
(declare-const MIRNominalTypeEnum_Float64 Int)
(declare-const MIRNominalTypeEnum_String Int)
(declare-const MIRNominalTypeEnum_UUID Int)
(declare-const MIRNominalTypeEnum_LogicalTime Int)
(declare-const MIRNominalTypeEnum_CryptoHash Int)
(declare-const MIRNominalTypeEnum_ByteBuffer Int)
(declare-const MIRNominalTypeEnum_ISOTime Int)
(declare-const MIRNominalTypeEnum_Tuple Int)
(declare-const MIRNominalTypeEnum_Record Int)
(declare-const MIRNominalTypeEnum_Regex Int)

(assert (= MIRNominalTypeEnum_BigInt MIRNominalTypeEnum_nscore__bigintI0I))
(assert (= MIRNominalTypeEnum_Bool MIRNominalTypeEnum_nscore__boolI1I))
(assert (= MIRNominalTypeEnum_ByteBuffer MIRNominalTypeEnum_nscore__bytebufferI5I))
(assert (= MIRNominalTypeEnum_CryptoHash MIRNominalTypeEnum_nscore__cryptohashI6I))
(assert (= MIRNominalTypeEnum_Float64 MIRNominalTypeEnum_nscore__float64I7I))
(assert (= MIRNominalTypeEnum_ISOTime MIRNominalTypeEnum_nscore__isotimeI9I))
(assert (= MIRNominalTypeEnum_Int MIRNominalTypeEnum_nscore__intI8I))
(assert (= MIRNominalTypeEnum_LogicalTime MIRNominalTypeEnum_nscore__logicaltimeI12I))
(assert (= MIRNominalTypeEnum_None MIRNominalTypeEnum_nscore__noneI13I))
(assert (= MIRNominalTypeEnum_Record MIRNominalTypeEnum_nscore__recordI28I))
(assert (= MIRNominalTypeEnum_Regex MIRNominalTypeEnum_nscore__regexI14I))
(assert (= MIRNominalTypeEnum_String MIRNominalTypeEnum_nscore__stringI15I))
(assert (= MIRNominalTypeEnum_Tuple MIRNominalTypeEnum_nscore__tupleI31I))
(assert (= MIRNominalTypeEnum_UUID MIRNominalTypeEnum_nscore__uuidI16I))

(declare-fun nominalDataKinds (Int) StructuralSpecialTypeInfo)
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__bigintI0I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__boolI1I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__buffercompressionI2I) (StructuralSpecialTypeInfo@cons true false true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__bufferencodingI3I) (StructuralSpecialTypeInfo@cons true false true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__bufferformatI4I) (StructuralSpecialTypeInfo@cons true false true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__bytebufferI5I) (StructuralSpecialTypeInfo@cons false false false)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__cryptohashI6I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__float64I7I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__intI8I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__isotimeI9I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I) (StructuralSpecialTypeInfo@cons false true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__logicaltimeI12I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__noneI13I) (StructuralSpecialTypeInfo@cons true true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__regexI14I) (StructuralSpecialTypeInfo@cons false false false)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__stringI15I) (StructuralSpecialTypeInfo@cons false true true)))
(assert (= (nominalDataKinds MIRNominalTypeEnum_nscore__uuidI16I) (StructuralSpecialTypeInfo@cons true true true)))

(define-fun bsqkey_get_nominal_type ((keyv BKeyValue)) Int
  (ite (= keyv bsqkey_none) MIRNominalTypeEnum_None
    (ite (is-bsqkey_bool keyv) MIRNominalTypeEnum_Bool
      (ite (is-bsqkey_int keyv) MIRNominalTypeEnum_Int
        (ite (is-bsqkey_bigint keyv) MIRNominalTypeEnum_BigInt
          (ite (is-bsqkey_string keyv) MIRNominalTypeEnum_String
            (ite (is-bsqkey_safestring keyv) (bsq_safestring_type (bsqkey_safestring_value keyv))
              (ite (is-bsqkey_stringof keyv) (bsq_stringof_type (bsqkey_stringof_value keyv))
                (ite (is-bsqkey_uuid keyv) MIRNominalTypeEnum_UUID
                  (ite (is-bsqkey_logicaltime keyv) MIRNominalTypeEnum_LogicalTime
                    (ite (is-bsqkey_cryptohash keyv) MIRNominalTypeEnum_CryptoHash
                      (ite (is-bsqkey_enum keyv) (bsq_enum_type (bsqkey_enum_value keyv))
                        (ite (is-bsqkey_idkeysimple keyv) (bsq_idkeysimple_type (bsqkey_idkeysimple_value keyv))
                          (bsq_idkeycompound_type (bsqkey_idkeycompound_value keyv))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun bsqterm_get_nominal_type ((term BTerm)) Int
  (ite (is-bsqterm_float64 term) MIRNominalTypeEnum_Float64
    (ite (is-bsqterm_key term) (bsqkey_get_nominal_type (bsqterm_key_value term))
      (ite (is-bsqterm_buffer term) (bsq_buffer_type (bsqterm_buffer_value term))
        (ite (is-bsqterm_bufferof term) (bsq_bufferof_type (bsqterm_bufferof_value term))
          (ite (is-bsqterm_bytebuffer term) MIRNominalTypeEnum_ByteBuffer
            (ite (is-bsqterm_isotime term) MIRNominalTypeEnum_ISOTime
              (ite (is-bsqterm_regex term) MIRNominalTypeEnum_Regex
                (ite (is-bsqterm_tuple term) MIRNominalTypeEnum_Tuple
                  (ite (is-bsqterm_record term) MIRNominalTypeEnum_Record
                    (bsqterm_object_type term)
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun bsqkeyless_basetypes ((k1 BKeyValue) (k2 BKeyValue)) Bool
  (let ((k1t (bsqkey_get_nominal_type k1)) (k2t (bsqkey_get_nominal_type k2)))
    (ite (not (= k1t k2t))
      (< k1t k2t)
      (ite (and (= k1 bsqkey_none) (= k2 bsqkey_none)) false
        (ite (and (is-bsqkey_bool k1) (is-bsqkey_bool k2)) (and (not (bsqkey_bool_value k1)) (bsqkey_bool_value k2))
          (ite (and (is-bsqkey_int k1) (is-bsqkey_int k2)) (< (bsqkey_int_value k1) (bsqkey_int_value k2))
            (ite (and (is-bsqkey_bigint k1) (is-bsqkey_bigint k2)) (< (bsqkey_bigint_value k1) (bsqkey_bigint_value k2))
              (ite (and (is-bsqkey_string k1) (is-bsqkey_string k2)) (str.< (bsqkey_string_value k1) (bsqkey_string_value k2))
                (ite (and (is-bsqkey_safestring k1) (is-bsqkey_safestring k2)) (str.< (bsq_safestring_value (bsqkey_safestring_value k1)) (bsq_safestring_value (bsqkey_safestring_value k2)))
                  (ite (and (is-bsqkey_stringof k1) (is-bsqkey_stringof k2)) (str.< (bsq_stringof_value (bsqkey_stringof_value k1)) (bsq_stringof_value (bsqkey_stringof_value k2)))
                    (ite (and (is-bsqkey_uuid k1) (is-bsqkey_uuid k2)) (str.< (bsq_uuid_value (bsqkey_uuid_value k1)) (bsq_uuid_value (bsqkey_uuid_value k2)))
                      (ite (and (is-bsqkey_logicaltime k1) (is-bsqkey_logicaltime k2)) (< (bsq_logicaltime_value (bsqkey_logicaltime_value k1)) (bsq_logicaltime_value (bsqkey_logicaltime_value k2)))
                        (ite (and (is-bsqkey_cryptohash k1) (is-bsqkey_cryptohash k2)) (str.< (bsq_cryptohash_value (bsqkey_cryptohash_value k1)) (bsq_cryptohash_value (bsqkey_cryptohash_value k2)))
                          (< (bsq_enum_value (bsqkey_enum_value k1)) (bsq_enum_value (bsqkey_enum_value k2)))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )   
    )
  )
)

(define-fun bsqkeyless_identitysimple ((idtype Int) (k1 bsq_idkeysimple) (k2 bsq_idkeysimple)) Bool
;;
;;TODO -- need to gas bound and generate this (and bsqkeyless programatically)
;;
false
)

(define-fun bsqkeyless_identitycompound ((idtype Int) (k1 bsq_idkeycompound) (k2 bsq_idkeycompound)) Bool
;;
;;TODO -- need to gas bound and generate this (and bsqkeyless programatically)
;;
false
)

(define-fun bsqkeyless ((k1 BKeyValue) (k2 BKeyValue)) Bool
  (let ((k1t (bsqkey_get_nominal_type k1)) (k2t (bsqkey_get_nominal_type k2)))
    (ite (not (= k1t k2t))
      (< k1t k2t)
      (ite (and (is-bsqkey_idkeycompound k1) (is-bsqkey_idkeycompound k2))
        (bsqkeyless_identitycompound k1t (bsqkey_idkeycompound_value k1) (bsqkey_idkeycompound_value k2))
        (ite (and (is-bsqkey_idkeysimple k1) (is-bsqkey_idkeysimple k2))
          (bsqkeyless_identitysimple k1t (bsqkey_idkeysimple_value k1) (bsqkey_idkeysimple_value k2))
          (bsqkeyless_basetypes k1 k2)
        )
      )
    )
  )
)

(declare-const StructuralSpecialTypeInfo@Clear StructuralSpecialTypeInfo)
(assert (= StructuralSpecialTypeInfo@Clear (StructuralSpecialTypeInfo@cons true true true)))

(define-fun getStructuralSpecialTypeInfoTerm ((term BTerm)) StructuralSpecialTypeInfo
  (ite (= term bsqterm@clear) StructuralSpecialTypeInfo@Clear
    (ite (is-bsqterm_tuple term) (bsq_tuple_concepts (bsqterm_tuple_value term))
      (ite (is-bsqterm_record term) (bsq_record_concepts (bsqterm_record_value term))
        (nominalDataKinds (bsqterm_get_nominal_type term))
      )
    )
  )
)

(define-fun mergeStructuralSpecialTypeInfo ((st1 StructuralSpecialTypeInfo) (st2 StructuralSpecialTypeInfo)) StructuralSpecialTypeInfo
  (StructuralSpecialTypeInfo@cons (and (StructuralSpecialTypeInfo$PODType st1) (StructuralSpecialTypeInfo$PODType st2)) (and (StructuralSpecialTypeInfo$APIType st1) (StructuralSpecialTypeInfo$APIType st2)) (and (StructuralSpecialTypeInfo$Parsable st1) (StructuralSpecialTypeInfo$Parsable st2)))
)

(define-fun @fj ((term BTerm) (sti StructuralSpecialTypeInfo)) StructuralSpecialTypeInfo
  (mergeStructuralSpecialTypeInfo (getStructuralSpecialTypeInfoTerm term) sti)
)

(declare-const @int_min Int)
(assert (= @int_min -9007199254740991))

(declare-const @int_max Int)
(assert (= @int_max 9007199254740991))

(define-fun @int_unsafe ((v Int)) Bool
  (or (< v @int_min) (> v @int_max))
)



(declare-const bsqterm_none BTerm)
(assert (= bsqterm_none (bsqterm_key bsqkey_none)))

(declare-const bsqidkey_array_empty (Array Int BKeyValue))
(assert (= bsqidkey_array_empty ((as const (Array Int BKeyValue)) bsqkey_none)))

(declare-const bsqtuple_array_empty (Array Int BTerm))
(assert (= bsqtuple_array_empty ((as const (Array Int BTerm)) bsqterm@clear)))

(declare-const bsqrecord_array_empty (Array String BTerm))
(assert (= bsqrecord_array_empty ((as const (Array String BTerm)) bsqterm@clear)))

(declare-const nscore__list_t_nscore__int__collection_data_array_emptyI11I (Array Int Int))

(declare-datatypes (
      (ErrorCode 0)
      (Result@Bool 0)
    (Result@Int 0)
    ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id String)) )
    ( (result_success@Bool (result_success_value@Bool Bool)) (result_error@Bool (result_error_code@Bool ErrorCode)) )
    ( (result_success@Int (result_success_value@Int Int)) (result_error@Int (result_error_code@Int ErrorCode)) )
))

(declare-const mirconceptsubtypearray_empty (Array Int Bool))
(assert (= mirconceptsubtypearray_empty ((as const (Array Int Bool)) false)))



(declare-const MIRConceptSubtypeArray$nscore__anyI17I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__anyI17I (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true) MIRNominalTypeEnum_nscore__bytebufferI5I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__float64I7I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__isotimeI9I true) MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__noneI13I true) MIRNominalTypeEnum_nscore__recordI28I true) MIRNominalTypeEnum_nscore__regexI14I true) MIRNominalTypeEnum_nscore__stringI15I true) MIRNominalTypeEnum_nscore__tupleI31I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__apitypeI18I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__apitypeI18I (store (store (store (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__float64I7I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__isotimeI9I true) MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__noneI13I true) MIRNominalTypeEnum_nscore__stringI15I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__apivalueI19I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__apivalueI19I (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true) MIRNominalTypeEnum_nscore__bytebufferI5I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__float64I7I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__isotimeI9I true) MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__noneI13I true) MIRNominalTypeEnum_nscore__stringI15I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__enumI21I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__enumI21I (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true)))
(declare-const MIRConceptSubtypeArray$nscore__expandoable_t_nscore__int_I22I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__expandoable_t_nscore__int_I22I (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true)))
(declare-const MIRConceptSubtypeArray$nscore__keytypeI24I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__keytypeI24I (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__noneI13I true) MIRNominalTypeEnum_nscore__stringI15I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__objectI25I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__objectI25I (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true)))
(declare-const MIRConceptSubtypeArray$nscore__parsableI26I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__parsableI26I (store (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__float64I7I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__isotimeI9I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__noneI13I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__podtypeI27I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__podtypeI27I (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__float64I7I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__isotimeI9I true) MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__noneI13I true) MIRNominalTypeEnum_nscore__stringI15I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__recordI28I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__recordI28I (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__recordI28I true)))
(declare-const MIRConceptSubtypeArray$nscore__someI29I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__someI29I (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__bigintI0I true) MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__buffercompressionI2I true) MIRNominalTypeEnum_nscore__bufferencodingI3I true) MIRNominalTypeEnum_nscore__bufferformatI4I true) MIRNominalTypeEnum_nscore__bytebufferI5I true) MIRNominalTypeEnum_nscore__cryptohashI6I true) MIRNominalTypeEnum_nscore__float64I7I true) MIRNominalTypeEnum_nscore__intI8I true) MIRNominalTypeEnum_nscore__isotimeI9I true) MIRNominalTypeEnum_nscore__list_t_nscore__int_I10I true) MIRNominalTypeEnum_nscore__logicaltimeI12I true) MIRNominalTypeEnum_nscore__recordI28I true) MIRNominalTypeEnum_nscore__regexI14I true) MIRNominalTypeEnum_nscore__stringI15I true) MIRNominalTypeEnum_nscore__tupleI31I true) MIRNominalTypeEnum_nscore__uuidI16I true)))
(declare-const MIRConceptSubtypeArray$nscore__truthyI30I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__truthyI30I (store (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__boolI1I true) MIRNominalTypeEnum_nscore__noneI13I true)))
(declare-const MIRConceptSubtypeArray$nscore__tupleI31I (Array Int Bool))
(assert (= MIRConceptSubtypeArray$nscore__tupleI31I (store mirconceptsubtypearray_empty MIRNominalTypeEnum_nscore__tupleI31I true)))





(declare-fun @list_all$fn__list_example_bsq_5__102I36I (nscore__list_t_nscore__int_I10I) Bool)
(define-fun nscore__list__s_size_t_nscore__int_I34I ((lI33I nscore__list_t_nscore__int_I10I)) Result@Int 
  (result_success@Int (nscore__list_t_nscore__int_I10I@@size lI33I))
)
(define-fun fn__list_example_bsq_5__102I36I ((xI35I Int)) Result@Bool 
(let ((__tmp_0I37I (< 0 xI35I)))
    (let ((___ir_ret__I38I __tmp_0I37I))
      (let (($return ___ir_ret__I38I))
        (result_success@Bool $return)
      )
    )
  ))
(define-fun nscore__list__s_all_t_nscore__int__list_example_bsq_5_0_I39I ((lI33I nscore__list_t_nscore__int_I10I)) Result@Bool 
  (result_success@Bool (@list_all$fn__list_example_bsq_5__102I36I lI33I))
)
(define-fun nscore__list__allof_t_nscore__int__list_example_bsq_5_0___llogic_done_3I41I ((__tmp_0_2I40I Bool)) Result@Bool 
(let ((___ir_ret__I38I __tmp_0_2I40I))
    (let (($return ___ir_ret__I38I))
      (result_success@Bool $return)
    )
  ))
(define-fun nscore__list__allof_t_nscore__int__list_example_bsq_5_0_I43I ((thisI42I nscore__list_t_nscore__int_I10I)) Result@Bool 
(let ((@tmpvar@0 (nscore__list__s_size_t_nscore__int_I34I thisI42I)))
    (ite (is-result_error@Int @tmpvar@0)
      (result_error@Bool (result_error_code@Int @tmpvar@0))
      (let ((__tmp_2I44I (result_success_value@Int @tmpvar@0)))
        (let ((__tmp_1I45I (= __tmp_2I44I 0)))
          (ite __tmp_1I45I
            (let ((__tmp_0_1I46I true))
              (let ((@tmpvar@1 (nscore__list__allof_t_nscore__int__list_example_bsq_5_0___llogic_done_3I41I __tmp_0_1I46I)))
                (ite (is-result_error@Bool @tmpvar@1)
                  @tmpvar@1
                  (let ((__tmp_100001I47I (result_success_value@Bool @tmpvar@1)))
                    (let (($return __tmp_100001I47I))
                      (result_success@Bool $return)
                    )
                  )
                )
              )
            )
            (let ((@tmpvar@2 (nscore__list__s_all_t_nscore__int__list_example_bsq_5_0_I39I thisI42I)))
              (ite (is-result_error@Bool @tmpvar@2)
                @tmpvar@2
                (let ((__tmp_5I48I (result_success_value@Bool @tmpvar@2)))
                  (let ((__tmp_0I37I __tmp_5I48I))
                    (let ((@tmpvar@3 (nscore__list__allof_t_nscore__int__list_example_bsq_5_0___llogic_done_3I41I __tmp_0I37I)))
                      (ite (is-result_error@Bool @tmpvar@3)
                        @tmpvar@3
                        (let ((__tmp_100000I49I (result_success_value@Bool @tmpvar@3)))
                          (let (($return __tmp_100000I49I))
                            (result_success@Bool $return)
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ))
(define-fun nsmain__mainI50I () Result@Int 
(let ((__tmp_0I37I (nscore__list_t_nscore__int_I10I@cons 2 (store (store nscore__list_t_nscore__int__collection_data_array_emptyI11I 0 101) 1 1))))
    (let ((lI33I __tmp_0I37I))
      (let ((@tmpvar@4 (nscore__list__allof_t_nscore__int__list_example_bsq_5_0_I43I lI33I)))
        (ite (is-result_error@Bool @tmpvar@4)
          (result_error@Int (result_error_code@Bool @tmpvar@4))
          (let ((__tmp_3I51I (result_success_value@Bool @tmpvar@4)))
            (ite __tmp_3I51I
              (let ((___ir_ret__I38I 0))
                (let (($return ___ir_ret__I38I))
                  (result_success@Int $return)
                )
              )
              (result_error@Int (result_error 0))
            )
          )
        )
      )
    )
  ))
(assert 
(forall 
((l nscore__list_t_nscore__int_I10I) (i Int)) 
(=> (@list_all$fn__list_example_bsq_5__102I36I l) 
(result_success_value@Bool (fn__list_example_bsq_5__102I36I (select (nscore__list_t_nscore__int_I10I@@entries l) i))) 
)
)
)

(assert 
(forall 
((l nscore__list_t_nscore__int_I10I)) 
(=> (= (nscore__list_t_nscore__int_I10I@@size l) 0)
(@list_all$fn__list_example_bsq_5__102I36I l))
)
)



(declare-const @smtres@ Result@Int)
(assert (= @smtres@ nsmain__mainI50I))
(assert (not (and (is-result_error@Int @smtres@) (is-result_bmc (result_error_code@Int @smtres@)))))
(assert (is-result_error@Int @smtres@))

(check-sat)

