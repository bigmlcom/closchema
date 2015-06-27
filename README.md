# Closchema

A clojure library that implements
[JSON schema](http://json-schema.org/) validation.

This library is distributed under the MIT license (see LICENSE).

[![Clojars Project](http://clojars.org/bigml/closchema/latest-version.svg)](http://clojars.org/bigml/closchema)

## Examples

```
(require '[closchema.core :as schema])
=> nil
(schema/validate {:type "array" :items {:type "string"}} ["1" "2"])
=> true
(schema/validate {:type "array" :items {:type "string"}} ["1" 2])
=> false
(schema/report-errors
  (schema/validate {:type "array" :items {:type "string"}} ["1" 2 {}]))
=> '(.. errors )
```

## JSON Object Referencing (Schema extension)

This library implements the **file-based** part of referencing described here
(at the end of the post):

http://www.sitepen.com/blog/2008/10/31/json-schema/

Right now, you can only specify filenames (not full URLs), and they must be
located in your Java resources directory, as specified on the classpath.
**There is no ID-based referencing as of this readme.**

With this extension, one can specify a reference to a file containing a schema
using the key `$ref` when describing a property:

```json
{
    "type" : "object",
    "properties" : {
        "id" : {"type" : "integer"},
        "address" : {"$ref" : "path/to/file"}
    }
}
```

Reading is lazy, so the schema is not read until we hit it at validation time.
Files are read using `slurp` and `clojure.data.json`.  Schema references
are cached using `memoize`.

## Inheritance with `extends`

`extends` is implemented as it is described here:

http://www.sitepen.com/blog/2009/09/02/json-namespacing/

Anything validating as `:type "object"` can use `extends`.  The value of `
extends`  can be any valid schema, or any array of schemas.  This specifies
that, as part of its validation, this object must validate against the
specified schema or schemas.

Thus, the following produces a schema specifying an `:id` that is an `integer`,
and also specifying that an object must additionally validate against the
schema in `"file1.json"`.

```json
{
    "type" : "object",
    "extends" : {"$ref" : "file1.json"},
    "properties" : {
        "id" : {"type" : "integer"}
    }
}
```

Multiple inheritance also has the expected semantics:

```json
{
    "type" : "object",
    "extends" : [{"$ref" : "file1.json"}, {"$ref" : "file2.json"}],
    "properties" : {
        "id" : {"type" : "integer"}
    }
}
```

A word of caution: If `:additionalProperties false` is set in a "child"
schema, nothing will validate against it unless the parent schema(s) is/are
empty.  That is, `:additionalProperties` takes precedence over `:extends`.

## TODO

The entire spec http://tools.ietf.org/html/draft-zyp-json-schema-03 is
not implemented yet. We'll gradually support more features as needed.
