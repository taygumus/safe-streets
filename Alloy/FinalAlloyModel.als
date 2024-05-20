//--------Signatures--------

abstract sig AccountStatus {}

one sig Active extends AccountStatus {}

one sig Created extends AccountStatus {}

// All the status for reports

abstract sig ReportStatus {}

one sig Accepted extends ReportStatus {}

one sig Refused extends ReportStatus {}

one sig Validated extends ReportStatus {}

// Actors

abstract sig User {}

abstract sig PA extends User {}

// Used in order to collect all the Users for each kind of statistic

one sig EndUser {composedBy: some User}

one sig Municipality extends PA {}

one sig PoliceOffice extends PA {}

sig Citizen extends User {
	fiscalCode: one FiscalCode,
	status: one AccountStatus
}

// Fiscal code

sig FiscalCode {}

sig Location {}

sig Date {}

sig LicensePlate {}

abstract sig TicketStatus {}

one sig IssuedTicket extends TicketStatus {}

one sig NotIssuedTicket extends TicketStatus {}

// One report is associated to one citizen through its fiscal code

sig Report {
	status: one ReportStatus,
	fiscalCode: one FiscalCode,
	licensePlate: one LicensePlate,  
	date : one Date,
	location: one Location,
	type: one TypeInfraction
}

sig Violation {
	licensePlate: one LicensePlate,
	reports: set Report,
	date : one Date,
	location: one Location, 
	ticketStatus: one TicketStatus,
	type: one TypeInfraction
}

sig Feedback {
	violation: one Violation,
	madeBy: PoliceOffice
}

// Statistics - Two types of statistics are defined in order to highlight the different level of visibility based on the role

abstract sig Statistic {}

one sig StatBase extends Statistic  {
	accessibility: EndUser
}

one sig  StatAdvanced extends Statistic {
	accessibility: some PA
}

// Statistic that refers to advanced functionality 2

one sig TIStatistics extends Statistic {
	accessibility: some PA
}

sig Suggestion {}

sig TypeInfraction {
	suggestion:Suggestion
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

//--------Facts--------

// A report associated to a violation is validated

fact AViolationContainsOnlyValidatedReport {
	all r: Report | r.status = Validated <=> r in Violation.reports
}

// Fiscal code is unique
fact UniqueFiscalCode {
	no c:Citizen |  c.fiscalCode in (Citizen-c).fiscalCode
}

fact AViolationExists {
	// All the reports associated in a violation have the license plate equal to the one in the violation
	all v: Violation | all r: v.reports | v.licensePlate = r.licensePlate

	// A report is used only for a violation
	no r: Report, v: Violation, s: Violation | v != s and r in v.reports and r in s.reports

	// Violation is created when we have at least 2 reports
	all v: Violation | #v.reports > 1
}

fact singleEvent {
	// Data, position and license plate define an event. All reports of the same event are treated in the same way
	no r, r' : Report | r.date = r'.date and r.location = r'.location and r.licensePlate = r'.licensePlate and r.status != r'.status and r=r'
	
	// No more than one report of the same citizen about the same event
	no r,r' : Report | r.date = r'.date and r.location = r'.location and r.licensePlate = r'.licensePlate and r.fiscalCode = r'.fiscalCode and r != r'
	
	// Date and Location are the same in the reports as in the Violation they are in
	all v: Violation, r: v.reports | r.date = v.date and r.location = v.location
}

fact noMoreThanOneReportInValidation {
	// There can be at most one report in validation about an event. With at least two reports accepted, a violation can be generated and the reports become validated
	no r : Report, r':(Report-r) | r.date = r'.date and  r.location = r'.location and r.licensePlate = r'.licensePlate and r.fiscalCode != r'.fiscalCode  and r.status=Accepted and r'.status=Accepted
}

// Each of these needs a parent. They cannot float in the model
fact noFloatingEntities {
	all d : Date | d in Report.date
	all loc : Location | loc in Report.location
	all fc : FiscalCode | fc in Citizen.fiscalCode
	all lp : LicensePlate | lp in Report.licensePlate
	all tp:TypeInfraction| tp in Violation.type
	all sg:Suggestion| sg in TypeInfraction.suggestion
}

fact citizenMustBeActiveInOrderToReport {
	no c: Citizen | c.status = Created and c.fiscalCode in Report.fiscalCode
}

fact feedbackIssued {
	// No more than one feedback for violation
	no  f,f'' : Feedback | f != f'' and f.violation = f''.violation

	// No feedback with more than one violation
	no v,v': Violation, f : Feedback | v != v' and f.violation = v and f.violation = v'

	// No issued status without feedback 
	no v : Violation | (v.ticketStatus = NotIssuedTicket and v in Feedback.violation) or ( v.ticketStatus = IssuedTicket and v not in Feedback.violation)
}

// Define which kind of user can access to each type of statistic
fact defineAccessibilityContrainst {
	all u : User | u in EndUser.composedBy
	all u : PA | u in StatAdvanced.accessibility
	all u : PA | u in TIStatistics.accessibility
}

fact cannotExistTwoViolationsThatAreTheSame {
	no v1,v2 : Violation | v1 != v2 and v1.date = v2.date and v1.location = v2.location and v1.licensePlate = v2.licensePlate
}

fact typeViolationIsTheSameOfItsReports {
	all v: Violation, r: v.reports | r.type = v.type
}

// For each type of infraction there is only a suggestion
fact differentInfractionsHaveDifferentSuggestions {
	no t,s:TypeInfraction | t!=s and s.suggestion = t.suggestion
}

// In order to reduce the graphic complexity, we reduced the threshold for establishing if an area is unsafe
fact NoDuplicateIncidents {
	no i1,i2: Incident | i1.location = i2.location and i1.date=i2.date and i1 != i2
	all un:UnsafeArea | #un.incidents > 1
	all ua: UnsafeArea, disj i1,i2 : ua.incidents | i1.location =i2.location and i1.location = ua.location
}

// Unsafe area has the same location as for the violations in it
fact NoLocationInUnsafeAreaNotInViolation {
	// To be an unsafe area, it must have 3 or more violations
	all ua : UnsafeArea| #ua.violations>1

	// Given two different unsafe areas, they do not have the same location. For all the unsafe areas
	no ua, ua' : UnsafeArea | ua != ua' and ua.location = ua'.location

	// For all the violations associated with an unsafe area, the location is the same
	all ua: UnsafeArea, disj v,v' : ua.violations | v.location =v'.location and v.location = ua.location
}

//--------Assertions--------

// There is no report that is not validated but there is already a violation
assert noSameReportForTheSameEvent {
	no disj r1,r2 : Report | r1.location = r2.location and r1.date = r2.date and r1.licensePlate = r2.licensePlate  and r1.fiscalCode = r2.fiscalCode
}

assert noInvalidStateCondition {
	all r: Report | r.status = Validated iff r in Violation.reports
	all c: Citizen | all r: Report | r.fiscalCode = c.fiscalCode implies  c.status = Active 
	all f: Feedback | all v: Violation | (f.violation = v iff v.ticketStatus = IssuedTicket) and (v.ticketStatus = NotIssuedTicket iff v not in Feedback.violation )
}

assert violationConsistency {
	no v1,v2 : Violation | v1 != v2 and v1.date = v2.date and v1.location = v2.location and v1.licensePlate = v2.licensePlate
	all v: Violation, r: v.reports | r.type = v.type
}

assert noDifferentReportLocationInViolation {
	all v: Violation | all r : v.reports | r.location = v.location and v.date = r.date
}

assert extractUnsafeAreas {
	all ua: UnsafeArea |  all v: Violation | all r: Report | (ua.location = v.location and v.location =  r.location) iff( v in ua.violations and r in v.reports)
	all r:Report|r.status=Validated or r.status = Accepted or r.status = Refused
}

check noSameReportForTheSameEvent for 4
check noDifferentReportLocationInViolation for 5
check extractUnsafeAreas for 3
check noInvalidStateCondition for 3
check violationConsistency for 5

// Generate basic service world
pred basicService {
	#Report = 4
	#Violation = 1
	#Citizen = 3
}

// Generate Advanced Function2 world
pred advancedFunction2 {
	#Report = 5
	#Violation = 2
	#Feedback = 1
	#Citizen = 3
}

// Generate Advanced Function1 world
pred advancedFunction1 {
	#Violation =3
	#UnsafeArea = 1
	#Date=2
	#Incident = 2
	#Location = 2
}

run basicService for 6
run advancedFunction1 for 8
run advancedFunction2 for 6
