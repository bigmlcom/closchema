(ns closchema.test.core
  (:require (cheshire [core :as cheshire])
            (closchema [core :as closchema :refer [validate]])
            (clojure.java [io :as io]))
  (:use clojure.test))

(def base-schema {:type "object"
                  :required true
                  :properties {:id {:type "number"
                                    :required true}
                               :name {:type "string"
                                      :required true}
                               :description {:type "string"}}})

;; Union type containing either an ID number or a first and last name
(def union-schema {:type ["integer" {:type "object"
                                     :required true
                                     :properties {:first-name
                                                  {:type "string"
                                                   :required true}
                                                  :last-name
                                                  {:type "string"
                                                   :required true}}}]
                   :required true})

(def read-schema {:type "object"
                  :required true
                  :properties {:person {:$ref "test1.json"
                                        :required true}
                               :dog-name {:type "string"
                                          :required true}}})

(def union-array {:type "array"
                  :required true
                  :items {:type ["integer"
                                 {:$ref "test1.json"}]}})

(def self-ref (cheshire/decode (slurp (io/resource "self-ref.json")) true))

(def extends-schema {:type "object"
                     :required true
                     :extends {:$ref "test2.json"}
                     :properties {:id {:type "integer"
                                       :required true}}})

(def extends-mult {:type "object"
                   :required true
                   :extends [{:$ref "test2.json"}
                             {:type "object"
                              :required true
                              :properties {:name {:type "string"
                                                  :required true}}}]})

(def json1-item {:name "Fred" :info {:odor "wet dog" :human? true}})

(deftest validate-properties
  (let [s base-schema]
    (is (validate s {:id 1 :name "shoe"})
        "should accept object with only required properties")
    (is (validate s {:id 1 :name "shoe" :description "style"})
        "should accept object with optional properties")
    (is (not (validate s {:id 1}))
        "should not accept when required property is not present")
    (is (not (validate s {:id "1" :name "bag"}))
        "should not accept when property type is incorrect")
    (is (validate s {:id 1 :name "test" :description nil})
        "should accept an optional property with value null")))

(deftest validate-false-additional-properties
  (let [s (merge base-schema {:additionalProperties false})]
    (is (not (validate s {:id 1 :name "wine" :age "13 years"}))
        "should not allow any properties that are not defined in schema")
    (is (validate s {:id 1 :name "wine" :description "good"})
        "should allow any properties that are defined in schema as optional")))

(deftest validate-additional-properties-schema
  (let [s (merge base-schema {:additionalProperties {:type "string"}})]
    (is (and (validate s
                       {:id 1 :name "wine" :age "13 years" :country "france"})
             (not (validate s {:id 1 :name "wine" :age 13})))
        "should enforce that all extra properties conform to the schema")))

(deftest validate-additional-properties-fields
  (let [s (assoc base-schema
            :properties (merge (base-schema :properties)
                               {:address  {:type "string" :required false}
                                :address2 {:type "string"
                                           :requires "address"
                                           :required false}}))]
    (is (validate s {:id 1 :name "john" :address "street"})
        "should validate with non-required")
    (is (validate s {:id 1 :name "john" :address "street" :address2 "country"})
        "should validate when both are present" )
    (is (not (validate s {:id 1 :name "john" :address2 "country"}))
        "should not validate nem required is not present")))

(deftest validate-pattern-properties
  (let [s (merge base-schema {:additionalProperties false :patternProperties {"^tes(t)+$" {:type "string"}}})]
    (is (not (validate s {:id 1 :name "wine" :age "13 years"}))
        "should not allow any properties that are not defined in schema")
    (is (validate s {:id 1 :name "wine" :test "good"})
        "should allow any properties that are defined in pattern")))

(deftest validate-items-any
  (is (and (validate {:type "array"} [ 1 2 3])
           (validate {:type "array" :items []} [1 "2" 3])
           (validate {:type "array"} (map identity [1 2 3]))
           (validate {:type "array"} #{1 2 3}))
      "should allow any items"))

(deftest validate-items-with-object-schema
  (let [s1 {:type "array" :items {:type "string"}}
        s2 {:type "array" :items {:type "object"
                                  :required true
                                  :properties {:name {:type "string"
                                                      :required true}}}}]
    (is (validate s1 []) "should accept empty array")
    (is (and (validate s1 ["a" "b" "c"])
             (validate s2 [{:name "half"} {:name "life"}]))
        "should accept homogenous array")
    (is (not (validate s1 ["a" "b" 3])) "should not accept heterogenous array")
    (is (not (validate s2 [{:name "quake"} {:id 1}]))
        "should not accept if inner item does not follow item schema")))

(deftest validate-items-with-schema-array
  (let [s {:type "array" :items [{:type "string"
                                  :required true}
                                 {:type "string"
                                  :required true}]}]
    (is (and (validate s ["a" "b"])
             (not (validate s ["a"]))
             (not (validate s ["a" 1])))
        "should enforce tuple typing")
    (is (and (validate s ["a" "b" "c"]) (validate s ["a" "b" 1 2 3 {}]))
        "should allow additional properties to be defined by default")))

(deftest validate-items-with-additional-properties
  (let [s {:type "array" :items [{:type "number"}]
           :additionalProperties {:type "string"}}]
    (is (and (validate s [1 "a" "b" "c"]) (not (validate s [1 2 "a"])))
        "should ensure type schema for additional properties")
    (is (not (validate s ["a" 1])) "should still enforce tuple typing")))

(deftest validate-items-with-additional-properties-disabled
  (let [s {:type "array" :items [{:type "number"}]
           :additionalProperties false}]
    (is (validate s [1]) "should be strict about tuple typing")
    (is (not (validate s [1 "a"])) "should be strict about tuple typing")))

(deftest validate-items-with-unique-items-set
  (let [s {:type "array" :uniqueItems true}]
    (is (validate s [1 2 3]) "of type numbers")
    (is (validate s ["a" "b"]) "of type strings")
    (is (validate s [{:a 1} {:b 1} {:a 2}]) "of type objects")
    (is (not (validate s [1 1])) "of type numbers")
    (is (not (validate s ["a" "b" "c" "b"])) "of type strings")
    (is (not (validate s [{:a 1} {:a 2} {:a 1}])) "of type objects")))

(deftest validate-items-with-bounds
  (let [s1 {:type "array" :minItems 2 :items {:type "number"}}
        s2 {:type "array" :maxItems 4 :items {:type "number"}}
        s11 {:type "array" :minItems 2 :maxItems 2 :items {:type "string"}}
        s12 (merge s1 s2)]
    (is (validate s1 [1 2]) "minimum length")
    (is (validate s12 [1 2]) "minimum length")
    (is (validate s11 ["1" "2"]) "minimum length")
    (is (validate s2 []) "minimum length")
    (is (not (validate s1 [1])) "minimum length")
    (is (not (validate s12 [1])) "minimum length")
    (is (not (validate s11 ["3"])) "minimum length")
    (is (validate s1 [1 2 3 4 5]) "maximum length")
    (is (validate s12 [1 2 3]) "maximum length")
    (is (validate s11 ["1" "2"]) "maximum length")
    (is (validate s2 []) "maximum length")
    (is (not (validate s2 [1 3 4 5 6 7])) "maximum length")
    (is (not (validate s12 [1 2 3 4 5])) "maximum length")
    (is (not (validate s11 ["1" "2" "3"])) "maximum length")))

(deftest validate-common-string
  (let [s {:type "string"}]
    (is (validate s "foobar") "should validate with string")))

(deftest validate-minimum-string
  (let [s {:type "string" :minLength 3}]
    (is (validate s "foobar") "validate if within the lengths")
    (is (not (validate s "fo")) "not validate if not within the lengths")))

(deftest validate-maximum-string
  (let [s {:type "string" :maxLength 5}]
    (is (validate s "fooba") "validate if within the lengths")
    (is (not (validate s "foobar")) "not validate if not within the lengths")))

(deftest validate-min-max-string
  (let [s {:type "string" :maxLength 5 :minLength 3}]
    (is (and (validate s "foo") (validate s "fooba"))
        "validate if within the lengths" )
    (is (and (not (validate s "fo")) (not (validate s "foobar")))
        "not validate if not within the lengths")))

(deftest validate-string-pattern
  (let [s {:type "string" :pattern "^[a-zA-Z0-9]+$"}]
    (is (and (validate s "fooBar")
             (validate s "fooBar123")
             (validate s "123fooBar"))
        "pattern matches")
    (is (and (not  (validate s "foo-Bar")) (not (validate s "foo_bar")))
        "pattern doesn't match"))
  (is (validate {:type "string" :pattern "es"} "expression")))

(deftest validate-common-numbers
  (let [s {:type "number"}]
    (is (and (validate s 1) (validate s -2) (validate s 3.5)) "is a number")
    (is (not (validate s "2")) "not a number")))

(deftest validate-max-number
  (let [s {:type '"number" :exclusiveMaximum 5}
        t {:type '"integer" :exclusiveMaximum 5}]
    (is (validate s 4) "lower than maximum")
    (is (and (not (validate s 6)) (not (validate s 5)))
        "greater or equal than maximum")
    (is (validate t 4) "lower than maximum")
    (is (and (not (validate t 6)) (not (validate t 5)))
        "greater or equal than maximum")))

(deftest validate-min-number
  (let [s {:type '"number" :exclusiveMinimum 2}
        t {:type '"integer" :exclusiveMinimum 2}]
    (is (validate s 3) "above minimum")
    (is (and (not (validate s 1)) (not (validate s 2)))
        "less or equal than minimum")
    (is (validate t 3) "above minimum")
    (is (and (not (validate t 1)) (not (validate t 2)))
        "less or equal than minimum")))

(deftest validate-max-number
  (let [s {:type '"number" :maximum 5}
        t {:type '"integer" :maximum 5}]
    (is (and (validate s 5) (validate s 4))
        "should validate if is lower or equal maximum")
    (is (not (validate s 6))
        "should not validate if not lower nor equal maximum")
    (is (and (validate t 5) (validate t 4))
        "should validate if is lower or equal maximum")
    (is (not (validate t 6))
        "should not validate if not lower nor equal maximum")))

(deftest validate-min-number
  (let [s {:type '"number" :minimum 2}
        t {:type '"integer" :minimum 2}]
    (is (and (validate s 3) (validate s 2))
        "should validate if is above or equal minimum")
    (is (not (validate s 1))
        "should not validate if not above nor equal minimum")
    (is (and (validate t 3) (validate t 2))
        "should validate if is above or equal minimum")
    (is (not (validate t 1))
        "should not validate if not above nor equal minimum")))

(deftest validate-divisible-number
  (let [s {:type "number" :divisibleBy 2}
        t {:type "integer" :divisibleBy 2}]
    (is (validate s 4) "number is divisible by 2")
    (is (not (validate s 5)) "if number it not divisible by 2")
    (is (validate t 4) "number is divisible by 2")
    (is (not (validate t 5)) "if number it not divisible by 2")))

(deftest validate-booleans
  (let [s {:type "boolean"}]
    (is (validate s false))
    (is (validate s true))
    (is (not (validate s "2"))))
  (let [s {:type "object" :properties {:header {:type "boolean"}}}]
    (is (validate s {:header true}))
    (is (validate s {:header false}))
    (is (not (validate s {:header 42})))))

(deftest reference
  (let [schema {:$ref "test1.json"}]
    (is (validate schema {:name "Jao" :info {:odor "roses" :human? true}}))
    (is (validate schema {:name "Fido" :info {:odor "wet dog" :human? false}}))
    (is (not (validate schema {:name "Fido" :info {:odor 4 :human? false}})))
    (is (not (validate schema {:name "Jao" :info {:odor "roses" :hu? true}})))
    (is (not (validate schema {:info {:odor "roses" :human? true}}))))
  (is (validate read-schema {:person json1-item :dog-name "wrinkles"}))
  (is (not (validate read-schema {:person 5 :dog-name "wrinkles"})))
  (is (not (validate read-schema {:person json1-item}))))

(deftest union
  (is (validate union-schema 5))
  (is (validate union-schema 123124))
  (is (not (validate union-schema 123.124)))
  (is (not (validate union-schema [1 2 3])))
  (is (validate union-schema {:first-name "charles" :last-name "parker"}))
  (is (not (validate union-schema {:first-name "charles" :last "parker"})))
  (is (not (validate union-schema {:first-name "charles" :last-name 4})))
  (is (not (validate union-schema {:first-name true :last-name "parker"}))))

(deftest array-union
  (is (validate union-array [1 2 3]))
  (is (validate union-array [1 2232 314567]))
  (is (validate union-array [10]))
  (is (validate union-array [10 json1-item 1423]))
  (is (validate union-array [json1-item json1-item]))
  (is (not (validate union-array [json1-item 23.5 json1-item])))
  (is (not (validate union-array [1 (assoc json1-item :name false) 2])))
  (is (not (validate union-array [1 "yes" 2 3]))))

(deftest array-self-ref
  (is (validate self-ref {:id 1}))
  (is (validate self-ref {:id 1 :children [{:id 5}]}))
  (is (validate self-ref {:id 1 :children [{:id 5} {:id 4}]}))
  (is (validate self-ref {:id 1 :children [{:id 5}
                                           {:id 4 :children [{:id 6}]}]}))
  (is (not (validate self-ref {:id 1 :children [3 4 5]})))
  (is (not (validate self-ref {:id 1.5 :children [{:id 5} {:id 4}]})))
  (is (not (validate self-ref {:id 1 :children [{:id 5} {:id "a"}]})))
  (is (not (validate self-ref {:id 1 :children [{:id 5}
                                                {:id 4
                                                 :children [{:i 6}]}]})))
  (is (not (validate self-ref {:id 1 :children [{:id 5}
                                                {:id "a"
                                                 :children [{:id 6}]}]}))))

(deftest null-in-objects
  (is (validate {:type "object" :properties {:id {:type "null"}}} {:id nil}))
  (is (not (validate {:type "object" :properties {:id {:type "null"}}}
                     {:id 4})))
  (is (not (validate {:type "object" :properties {:id {:type "null"}}}
                     {:id "a"})))
  (is (validate {:type "array" :items [{:type "null"} {:type "integer"}]}
                [nil 1]))
  (is (not (validate {:type "array" :items [{:type "null"} {:type "integer"}]}
                     [1 nil])))
  (is (validate {:type "array" :items [{:type "null"}
                                       {:type ["integer" "null"]}]}
                [nil nil])))

(deftest extends
  (is (validate extends-schema {:id 1 :human? false :odor "wet dog"}))
  (is (validate extends-schema {:id -1 :human? true :odor "roses"}))
  (is (not (validate extends-schema {:id 1 :humn? false :odor "wet-dog"})))
  (is (not (validate extends-schema {:id 1 :human? false :odor "rozes"})))
  (is (not (validate extends-schema {:id 1.1 :human? false :odor "roses"}))))

(deftest multiple-inheritance
  (is (validate extends-mult {:name "a" :human? false :odor "wet dog"}))
  (is (validate extends-mult {:name "b" :human? true :odor "roses"}))
  (is (not (validate extends-mult {:name "a" :odor "wet-dog"})))
  (is (not (validate extends-mult {:name 1 :human? false :odor "rozes"})))
  (is (not (validate extends-mult {:human? false :odor "roses"}))))

(deftest validate-any-type
  (is (validate {:type "any"} 1))
  (is (validate {:type "any"} [1 2 3]))
  (is (validate {:type "any"} {:a 3})))

(deftest validate-type-string-with-length-limits
  (is (not (validate {:type "string" :minLength 3} 1)))
  (is (not (validate {:type "string" :minLength 3} "ab")))
  (is (not (validate {:type "string" :maxLength 3} "abcd")))
  (is (not (validate {:type "string" :minLength 5 :maxLength 4} "abcde")))
  (is (validate {:type "string" :minLength 3 :maxLength 8} "abc"))
  (is (validate {:type "string" :minLength 3 :maxLength 8} "abcdef")))

(deftest validate-type-integer-with-vector-input
         (is (not (validate {:type "integer" :minimum 0} [1 2 3]))))

(deftest validate-type-array-with-number-input
         (is (not (validate {:type "array" :items {:type "integer"}} 1))))

;; Test all combinations of :required array
(deftest validate-with-new-required-keys
  ;; With no :required params, the key is not required
  (let [schema {:type "object"
                :properties {:id {:type "integer"}}}]
    (is (validate schema {})))

  ;; With an empty :required param, the key is not required
  (let [schema {:type "object" :required []
                :properties {:id {:type "integer"}}}]
    (is (validate schema {})))

  ;; With a :required param, the key is required
  (let [schema {:type "object" :required ["id"]
                :properties {:id {:type "integer"}}}]
    (is (not (validate schema {}))))

  ;; With a :required param, a keyword key is accepted
  (let [schema {:type "object" :required ["id"]
                :properties {:id {:type "integer"}}}]
    (is (validate schema {:id 12345})))

  ;; With a :required param, a string key is accepted
  (let [schema {:type "object" :required ["id"]
                :properties {:id {:type "integer"}}}]
    (is (validate schema {"id" 12345}))))

;; Test all combinations of :optional and :required
(deftest validate-with-required-or-optional-keys
  ;; With no :required or :optional params, the key is not required
  (let [schema {:type "object"
                            :properties {:id {:type "integer"}}}]
    (is (validate schema {})))

  ;; With a ":required true" param, the key is required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required true}}}]
    (is (not (validate schema {}))))

  ;; With a ":required false" param, the key is not required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required false}}}]
    (is (validate schema {})))

  ;; With an ":optional true" param, the key is not required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :optional true}}}]
    (is (validate schema {})))

  ;; With an ":optional false" param, the key is required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :optional false}}}]
    (is (not (validate schema {}))))

  ;; With ":required false" and ":optional true", the key is not required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required false
                                                 :optional true}}}]
    (is (validate schema {})))

  ;; With ":required true" and ":optional false", the key is required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required true
                                                 :optional false}}}]
    (is (not (validate schema {}))))

  ;; :required has precedence over :optional
  ;; With a ":required false"  ":optional false" param, the key is not required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required false
                                                 :optional false}}}]
    (is (validate schema {})))

  ;; :required has precedence over :optional
  ;; With a ":required true"  ":optional true" param, the key is required
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required true
                                                 :optional true}}}]
    (is (not (validate schema {})))))

(deftest validate-extra-validators
  (let [schema {:type "object" :properties {:id {:type "integer"
                                                 :required true}}}]
    (is (not (validate schema {:id "banana"})))
    (is (validate schema {:id "banana"}
                  :extra-validators {"integer" (fn [_] true)}))
    (is (not (validate schema {:id 10M})))
    (is (validate schema {:id 10M}
                  :extra-validators {"integer" (fn [x] (instance? BigDecimal x))}))))
