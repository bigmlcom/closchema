(ns closchema.core
  "This is JSON Schema in Clojure. See
   http://tools.ietf.org/html/draft-zyp-json-schema-02 Main purposed
   is to allow object validation, but schema metadata can be used for
   exposing contracts as well."
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
  (fn [errors] (= (count errors) 0)))


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
  (fn [schema instance]
    (cond
      (or (= (:type schema) "integer") (= (:type schema) "number")) ::value
      (string? schema) ::simple
      (vector? (:type schema)) ::union
      (:$ref schema) ::ref
      (:enum schema) ::enum
      (:type schema) (keyword (:type schema)))))

(defn validate
  "Entry point. A validation context is created and validation is
   dispatched to the appropriated multimethod."
  [schema instance]
  (with-validation-context
    (validate* schema instance)))

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

(defmethod ^:private validate* nil [schema instance]
  (validate (merge schema {:type default-type}) instance))

(defmethod ^:private validate* ::ref [schema instance]
  (validate (read-schema (:$ref schema)) instance))

;; This implementation of the multimethod is needed so that
;; Union types can be simple (e.g., "integer") or complex
;; (e.g., {:type "object" . . .}).  It causes strings like
;; "number" to constitute a valid json spec according to
;; validate, but that doesn't seem like a bad idea.
(defmethod ^:private validate* ::simple [schema instance]
  (validate {:type schema} instance))

;; Basically, try all the types with the error queue bound to a "fresh"
;; error queue.  If any of the resulting queues are empty at the
;; end, the instance validated and there's no reason to do anything.
;; If not, we pick one of the types (the first one, because why not?)
;; and put it through validation again to populate the error queue
(defmethod validate* ::union [schema instance]
  (let [errors (map #(binding [*errors* (atom '()) *path* []]
                       (validate % instance) @*errors*)
                    (:type schema))]
    (when-not (some empty? errors)
      (invalid :matches-no-type-in-union
               {:instance instance :errors (first (sort-by count errors))}))))

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


(defn- check-basic-type
  "Validate basic type definition for known types."
  [{t :type :as schema} instance]
  (or (and (nil? instance) (:optional schema))
      (let [t (or t default-type)
            types (if (coll? t) t (vector t))]
        (or (reduce #(or %1 %2)
                    (map (fn [t] ((basic-type-validations t) instance))
                         types))
            (invalid :type {:expected (map str types)
                            :actual (str (type instance))})))))


(defn- common-validate [schema instance]
  (check-basic-type schema instance)
  (comment TODO
           disallow
           extends))


(defmethod ^:private validate* :default [schema instance]
  (common-validate schema instance))


(defmethod ^:private validate* :object
  [{properties-schema :properties
    additional-schema :additionalProperties
    parent :extends
    :as schema} instance]

  (common-validate schema instance)

  ;; "parent" schema validation
  (when-not (nil? parent)
    (if (vector? parent)
      (doseq [s parent] (validate s instance))
      (validate parent instance)))

  ;; validate properties defined in schema
  (doseq [[property-name
           {optional :optional :as property-schema}] properties-schema]
    (let [prop-exists (and (map? instance) (contains? instance property-name))]
      (when-not (or prop-exists optional)
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


          (when-not (and (:optional :property-schema) (nil? instance))
            (walk-in instance property-name
                     (validate property-schema property))))))
    (invalid :objects-must-be-maps {:properties properties-schema}))


  ;; check additional properties
  (when (false? additional-schema)
    (if-let [additionals (set/difference (set (keys instance))
                                      (set (keys properties-schema)))]
      (when (> (count additionals) 0)
        (invalid :additional-properties-not-allowed
                 {:properties additionals})))))


(defmethod ^:private validate* :array
  [{items-schema :items
    unique? :uniqueItems :as schema} instance]

  (common-validate schema instance)

  ;; specific array validation
  (when (sequential? instance)
    (let [total (count instance)]
      (template/do-template [key op]
                   (if-let [expected (key schema)]
                     (when (op total expected)
                       (invalid key {:expected expected :actual total})))
                   :minItems <
                   :maxItems >))

    (if-let [unique? (:uniqueItems schema)]
      (reduce (fn [l r] (when-not (= l r)
                          (invalid :uniqueItems {:l l :r r}))
                r) instance))

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
        (validate obj-schema obj-array)))))


(defmethod ^:private validate* :string
  [schema instance]
  (common-validate schema instance)
  (when (string? instance)
    (when (schema :maxLength)
      (if-not (>= (schema :maxLength) (count instance))
        (invalid :max-length-exceeded
                 {:maxLength (schema :maxLength) :actual (count instance)})))
    (when (schema :minLength)
      (if-not (<= (schema :minLength) (count instance))
        (invalid :min-length-not-reached
                 {:minLength (schema :minLength) :actual (count instance)})))
    (when (schema :pattern)
      (if-not (.matches instance (schema :pattern))
        (invalid :pattern-not-matched
                 {:pattern (schema :pattern) :actual instance})))))

(defmethod ^:private validate* ::enum
  [schema instance]
  (if-not (true? (some #(= % instance) (schema :enum)))
    (invalid :value-not-in-enum {:enum (schema :enum) :value instance })))


(defmethod ^:private validate* ::value
  [schema instance]
  (common-validate schema instance)
  (when (number? instance)
    (when (schema :maximum)
      (if-not (>= (schema :maximum) instance)
        (invalid :value-greater-then-maximum
                 {:maximum (schema :maximum) :value instance })))

    (when (schema :minimum)
      (if-not (<= (schema :minimum) instance)
        (invalid :value-lower-then-minimum
                 {:minimum (schema :minimum) :value instance })))

    (when (schema :exclusiveMaximum)
      (if-not (> (schema :exclusiveMaximum) instance)
        (invalid :value-greater-or-equal-then-maximum
                 {:exclusiveMaximum (schema :exclusiveMaximum) :value instance })))

    (when (schema :exclusiveMinimum)
      (if-not (< (schema :minimumCanEqual) instance)
        (invalid :value-lower-or-equal-then-minimum
                 {:exclusiveMinimum (schema :exclusiveMinimum) :value instance })))

    (when (schema :divisibleBy)
      (if-not (= 0 (mod instance (schema :divisibleBy)))
        (invalid :value-not-divisible-by
                 {:divisibleBy (schema :divisibleBy) :value instance})))))
