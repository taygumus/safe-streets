
sig Location {}
sig Date {}

sig LicensePlate {}

// ACTOR

one sig Municipality {

occuredIncidents: set Incident,

} {
all i:Incident|i in occuredIncidents
}

sig Violation {
licensePlate: one LicensePlate,
date:one Date, // not forcing to be equal to the ones of the reports because there can be bias in the data
location: one Location,
type: one TypeInfraction
}

// ofc a violation is effective when constraints are satisfied 
fact AViolationExists {
no  v: Violation, s: Violation | v != s and v.licensePlate = s.licensePlate and v.date = s.date and v.location = s.location
}

fact noFloatingEntitties {
// each of these needs a parent. They cannot float in the model
all d : Date | d in Violation.date
all loc : Location | loc in Violation.location
all lp : LicensePlate | lp in Violation.licensePlate
all tp:TypeInfraction| tp in Violation.type
all sg:Suggestion| sg in TypeInfraction.suggestion
}

// function2
sig Suggestion {}

sig TypeInfraction {
suggestion:Suggestion
}

// for different types, there are no identical suggestions
fact s {
no t,s:TypeInfraction | t!=s and s.suggestion = t.suggestion
}

sig Incident {
location: one Location, 
date : one Date
}

sig UnsafeArea {
location : one Location,
violations: set Violation,
incidents: set Incident
}

fact NoDuplicateIncidents { // rename
// no duplicate Incidents
no i1,i2: Incident | i1.location = i2.location and i1.date=i2.date and i1 != i2

all un:UnsafeArea | #un.incidents > 1

all ua: UnsafeArea, disj i1,i2 : ua.incidents | i1.location = i2.location and i1.location = ua.location
}

fact NoLocationInUnsafeAreaNotInViolation { // (rename) there is no ua whose location is not in any violation, one or two violations
// to be an unsafe area, it must have 3 or more violations
all ua : UnsafeArea| #ua.violations>1 
// given two different unsafe areas, they do not have the same location. For all the unsafe areas
no ua, ua' : UnsafeArea | ua != ua' and ua.location = ua'.location
// for all the violations associated with an unsafe area, the location is the same
all ua: UnsafeArea, disj v,v' : ua.violations | v.location = v'.location and v.location = ua.location
}

pred advancedFunction1 {
#Violation = 3
#UnsafeArea = 1
#Date = 2
#Incident = 2
#Location = 2
}

run  advancedFunction1 for 8
