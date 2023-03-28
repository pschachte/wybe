# Proposed syntax for relational types

## Declaring entities
```
% The first parameter is set to be a unique identifier, so has to be unique
entity student(number: int, name: string, address: string)
entity subject(code: string, name: string)
```

## Creating entities
```
?stu_0 = student(0, "Steven Stone", "Mossdeep City")
?stu_1 = student(1, "Cynthia", "Celestial Town")
?sub = subject("COMP90048", "Declarative Programming")
```

## Retrieving an entity, given the corresponding (unique) key
```
student(0, ?stu_retrieve_0)
```
`stu_retrieve_0` will then be assigned to student "Steven Stone"

## Declaring a relation (between entities)
```
% Student is enrolled in Subject
relation enrolled(student: student, subject: subject)
```
Note: Could develop a syntactic sugar when the field name is the same as the entity name


## Relating entities
TODO: This produces side-effects. Propose a way to use resources.
```
enrolled(stu_0, sub)
enrolled(stu_1, sub)
```

## Retrieving entities, given a related entity
TODO: Needs refinement.
```
% Prints all students, given a subject
for enrolled(?stu, sub) {
    !println(stu)
}
```
