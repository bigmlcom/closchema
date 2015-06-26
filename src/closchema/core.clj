(ns closchema.core
  "JSON Schema validation in Clojure. See http://json-schema.org."
  (:require (cheshire [core :as cheshire])
            (clojure.java [io :as io])
            (clojure [set :as set]
                     [template :as template])))


(def ^:dynamic *errors*
  "Allow validation errors to be captured."
  nil)

(def ^:dynamic *path*
  "When walking an object, we keep a binding to current path."
  nil)

(def ^:dynamic process-errors
  "Default processing just outputs a boolean return."
  (comp zero? count))

(defn ^:private required?
  [schema]
  ; "required" has precedence over "optional",
  ; and properties are not required by default.
  (if-not (nil? (:required schema))
    (:required schema)
    (= false (:optional schema))))

(def ^{:doc "Known basic types."}
     basic-type-validations
     { "object" #(map? %)
       "array" #(or (seq? %) (and (coll? %) (not (map? %))))
       "string" #(string? %)
       "number" #(number? %)
       "integer" #(integer? %)
       "boolean" #(instance? Boolean %)
       "null" #(nil? %)
       "any" (constantly true)})

(defmacro with-validation-context
  "Defines a binding to allow access to the root object and to enable
   invalidations to be captured. This strategy removes the need of
   raising exceptions at every single invalid point, and allows
   context information to be used when reporting about errors. Nested
   contexts are just ignored."
  [& body]
  `(let [body# #(do ~@body (process-errors @*errors*))]
     (if-not *errors*
       (binding [*errors* (atom '()) *path* []]
         (body#))
       (body#))))


(defmacro ^:private walk-in
  "Step inside a relative path, from a previous object. This
   information is useful for reporting."
  [_ rel-path & body]
  `(binding [*path* (conj *path* ~rel-path)] ~@body))

(defmacro report-errors
  "Returns all errors, instead of simple boolean."
  [& args]
  `(binding [process-errors (fn [errors#] errors#)]
     (with-validation-context
       (do ~@args))))

(defmulti ^:private validate*
  "Dispatch on object type for validation. If not implemented,
   performs only basic type validation. Users can extend which types
   are supported by implementing validation for new types."
  (fn [schema instance validators]
    (cond
      (or (= (:type schema) "integer") (= (:type schema) "number")) ::value
      (string? schema) ::simple
      (vector? (:type schema)) ::union
      (:$ref schema) ::ref
      (:enum schema) ::enum
      (:type schema) (keyword (:type schema)))))

(defn- merge-fn
  "Merges two functions together and returns a function which ORs
  their results."
  [a b]
  (fn [x] (or (a x) (b x))))

(defn validate
  "Entry point. A validation context is created and validation is
   dispatched to the appropriated multimethod."
  [schema instance & {:keys [extra-validators passthrough-validators]}]
  (let [validators (merge (if extra-validators
                            (merge-with merge-fn
                                        basic-type-validations extra-validators)
                            basic-type-validations)
                          passthrough-validators)]
    (with-validation-context
      (validate* schema instance validators))))

(defn- read-schema* [loc]
  (cheshire/parse-string (slurp (io/resource loc)) true))

(def ^:private read-schema (memoize read-schema*))

(defmacro ^:private invalid
  "Register an invalid piece of data according to schema."
  [& args]
  (let [[path args] (if (keyword? (first args))
                      [nil args] [(first args) (rest args)])
        error (first args)
        data (second args)]
    `(let [error# (merge (when ~path {:ref ~path})
                         (when ~error {:error ~error})
                         (when ~data {:data ~data})
                         {:path (if ~path (conj *path* ~path) *path*)})]
       (when *errors* (swap! *errors* conj error#))
       (process-errors (list error#)))))

(def ^:private default-type "object")

(defmethod ^:private validate* nil [schema instance validators]
  (validate (merge schema {:type default-type}) instance
            :passthrough-validators validators))

(defmethod ^:private validate* ::ref [schema instance validators]
  (validate (read-schema (:$ref schema)) instance
            :passthrough-validators validators))

;; This implementation of the multimethod is needed so that
;; Union types can be simple (e.g., "integer") or complex
;; (e.g., {:type "object" . . .}).  It causes strings like
;; "number" to constitute a valid json spec according to
;; validate, but that doesn't seem like a bad idea.
(defmethod ^:private validate* ::simple [schema instance validators]
  (validate {:type schema} instance
            :passthrough-validators validators))

;; Basically, try all the types with the error queue bound to a "fresh"
;; error queue.  If any of the resulting queues are empty at the
;; end, the instance validated and there's no reason to do anything.
;; If not, we pick one of the types (the first one, because why not?)
;; and put it through validation again to populate the error queue
(defmethod validate* ::union [schema instance validators]
  (let [errors (map #(binding [*errors* (atom '()) *path* []]
                       (validate % instance
                                 :passthrough-validators validators)
                       @*errors*)
                    (:type schema))]
    (when-not (some empty? errors)
      (invalid :matches-no-type-in-union
               {:instance instance :errors (first (sort-by count errors))}))))


(defn- check-basic-type
  "Validate basic type definition for known types."
  [{t :type :as schema} instance validators]
  (or (and (nil? instance) (not (required? schema)))
      (let [t (or t default-type)
            types (if (coll? t) t (vector t))]
        (or (reduce some
                    (map (fn [t] ((validators t) instance))
                         types))
            (invalid :type {:expected (map str types)
                            :actual (str (type instance))})))))


(defn- common-validate [schema instance validators]
  (check-basic-type schema instance validators)
  (comment TODO
           disallow
           extends))


(defmethod ^:private validate* :default [schema instance validators]
  (common-validate schema instance validators))


(defn- find-matching-properties [instance [pattern schema]]
  (when-let [matches (keep identity
                           (map #(re-matches (re-pattern (name pattern))
                                             (name %))
                                (keys instance)))]
    (map #(vector (keyword (if (coll? %1) (first %1) %1)) %2)
         matches (repeat schema))))


(defn- absorb-properties
  [pattern-properties instance]
  (if (map? instance)
    (into {} (reduce concat (remove nil? (map (partial find-matching-properties
                                                       instance)
                                              pattern-properties))))
    {}))


(defmethod ^:private validate* :object
  [{properties-schema :properties
    additional-schema :additionalProperties
    pattern-properties :patternProperties
    required :required
    parent :extends
    :as schema} instance validators]
  (common-validate schema instance validators)

  ;; "parent" schema validation
  (when-not (nil? parent)
    (if (vector? parent)
      (doseq [s parent] (validate s instance
                                  :passthrough-validators validators))
      (validate parent instance :passthrough-validators validators)))

  ;; validate required properties defined in schema
  (when (vector? required)
    (doseq [property-name required]
      (let [prop-exists (and (map? instance)
                             (or (contains? instance property-name)
                                 (contains? instance (keyword property-name))))]
        (when-not prop-exists
          (invalid property-name :required)))))

  ;; validate properties defined in schema
  (let [properties-schema (merge properties-schema
                                 (absorb-properties pattern-properties instance))]
    (doseq [[property-name property-schema] properties-schema]
      (let [prop-exists (and (map? instance) (contains? instance property-name))]
        (when-not (or prop-exists
                      (not (required? property-schema)))
          (invalid property-name :required))))

    ;; validate instance properties (using individual or additional schema)
    (if (map? instance)
      (doseq [[property-name property] instance]
        (if-let [{requires :requires :as property-schema}
                 (or (and (map? properties-schema)
                          (properties-schema property-name))
                     (and (map? additional-schema) additional-schema))]
          (do
            (when (and requires property
                       (nil? (get instance (keyword requires))))
              (invalid requires :required {:required-by property-name}))
            (when-not (and (not (required? property-schema)) (nil? instance))
              (walk-in instance property-name
                       (validate property-schema property
                                 :passthrough-validators validators))))))
      (invalid :objects-must-be-maps {:properties properties-schema}))

    ;; check additional properties
    (when (false? additional-schema)
      (if-let [additionals (set/difference (set (keys instance))
                                           (set (keys properties-schema)))]
        (when (pos? (count additionals))
          (invalid :additional-properties-not-allowed
                   {:properties additionals}))))))


(defmethod ^:private validate* :array
  [{items-schema :items
    unique? :uniqueItems :as schema} instance validators]

  (common-validate schema instance validators)

  ;; specific array validation
  (when (sequential? instance)
    (let [total (count instance)]
      (template/do-template [key op]
                   (if-let [expected (key schema)]
                     (when (op total expected)
                       (invalid key {:expected expected :actual total})))
                   :minItems <
                   :maxItems >))

    (when unique?
      (reduce (fn [already x] (when (already x)
                                (invalid :uniqueItems {:duplicate x}))
                (conj already x))
              #{}
              instance))

    ;; treat array as object for further common validation
    (when items-schema
      (let [obj-array (if (and (coll? instance) (not (map? instance)))
                        (zipmap (range (count instance)) instance)
                        {0 instance})
            obj-schema (cond (or (and (map? items-schema)
                                      (:type items-schema))
                                 (:$ref items-schema))
                             {:type "object"
                              :additionalProperties items-schema}

                             (vector? items-schema)
                             (merge schema
                                    {:type "object"
                                     :properties
                                     (zipmap (range (count items-schema))
                                             items-schema)}))]
        (validate obj-schema obj-array :passthrough-validators validators)))))


(defmethod ^:private validate* :string
  [schema instance validators]
  (common-validate schema instance validators)
  (when (string? instance)
    (when (schema :maxLength)
      (when-not (>= (schema :maxLength) (count instance))
        (invalid :max-length-exceeded
                 {:maxLength (schema :maxLength) :actual (count instance)})))
    (when (schema :minLength)
      (when-not (<= (schema :minLength) (count instance))
        (invalid :min-length-not-reached
                 {:minLength (schema :minLength) :actual (count instance)})))
    (when (schema :pattern)
      (when-not (re-find (re-pattern (schema :pattern)) instance)
        (invalid :pattern-not-matched
                 {:pattern (schema :pattern) :actual instance})))))

(defmethod ^:private validate* ::enum
  [schema instance validators]
  (when-not (true? (some #(= % instance) (schema :enum)))
    (invalid :value-not-in-enum {:enum (schema :enum) :value instance})))


(defmethod ^:private validate* ::value
  [schema instance validators]
  (common-validate schema instance validators)
  (when (number? instance)
    (when (schema :maximum)
      (when-not (>= (schema :maximum) instance)
        (invalid :value-greater-than-maximum
                 {:maximum (schema :maximum)
                  :value instance})))

    (when (schema :minimum)
      (when-not (<= (schema :minimum) instance)
        (invalid :value-lower-than-minimum
                 {:minimum (schema :minimum)
                  :value instance})))

    (when (schema :exclusiveMaximum)
      (when-not (> (schema :maximum) instance)
        (invalid :value-greater-or-equal-than-maximum
                 {:exclusiveMaximum (schema :exclusiveMaximum)
                  :maximum (schema :maximum)
                  :value instance})))

    (when (schema :exclusiveMinimum)
      (when-not (< (schema :minimum) instance)
        (invalid :value-lower-or-equal-than-minimum
                 {:exclusiveMinimum (schema :exclusiveMinimum)
                  :minimum (schema :minimum)
                  :value instance})))

    (when (schema :divisibleBy)
      (when-not (zero? (mod instance (schema :divisibleBy)))
        (invalid :value-not-divisible-by
                 {:divisibleBy (schema :divisibleBy)
                  :value instance})))))
