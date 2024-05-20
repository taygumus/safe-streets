// STATUS
// account status
abstract sig AccountStatus {}
one sig Active extends AccountStatus {}
one sig Created extends AccountStatus {}

// all the status for reports
abstract sig ReportStatus {}
one sig Accepted extends ReportStatus {}
one sig Refused extends ReportStatus {}
one sig Validated extends ReportStatus {}

fact AViolationContainsOnlyValidatedReport {
// a report associated to a violation is validated
all r: Report | r.status = Validated <=> r in Violation.reports
}

// ACTOR
abstract sig User {}
abstract sig PA extends User {}

one sig EndUser {composedBy: some User}

one sig Municipality extends PA {}
one sig PoliceOffice extends PA {}

sig Citizen extends User {
fiscalCode: one FiscalCode,
status: one AccountStatus
}

// fiscal code
sig FiscalCode {}

sig DataAndLocation {}

sig LicensePlate {}

// fiscal code is unique
fact UniqueFiscalCode {
no c:Citizen |  c.fiscalCode in (Citizen-c).fiscalCode
}

// Report
// one report is associated to one citizen through its fiscal code
// standard information in a report form
sig Report {
status: one ReportStatus,
fiscalCode: one FiscalCode,
licensePlate: one LicensePlate,  // as we're testing the domain model, we assume that all the alg provides the license plate
dataLocation: one DataAndLocation
}

sig Violation {
licensePlate: one LicensePlate,
reports: set Report,
dataLocation: one DataAndLocation, // not forcing to be equal to the ones of the reports because there can be bias in the data
}

// ofc a violation is effective when constraints are satisfied 
fact AViolationExists {
// all the reports associated in a violation have the license plate equal to the one in the violation
all v : Violation |  v.reports.licensePlate = v.licensePlate and v.reports.dataLocation = v.dataLocation
--a report is used only for a violation
no r: Report, v: Violation, s: Violation | v != s and r in v.reports and r in s.reports
// violation is created when we have at least 2 reports
all v: Violation | #v.reports > 1
}

fact singleEvent {
// data, position and license plate define an event. All reports of the same event are treated in the same way
no r, r' : Report | r.dataLocation = r'.dataLocation and r.licensePlate = r'.licensePlate and r.status != r'.status and r=r'
no r,r' : Report | r.dataLocation = r'.dataLocation and r.licensePlate = r'.licensePlate and r.fiscalCode = r'.fiscalCode and r != r'
// do it also with events
}

fact noMoreThanOneReportInValidation {
// I can have at most one report in validation. With at least two reports accepted, I can fix a violation and validate the reports
no r : Report, r':(Report-r) | r.dataLocation = r'.dataLocation and r.licensePlate = r'.licensePlate and r.fiscalCode != r'.fiscalCode and r.status = Accepted and r'.status = Accepted
}

fact noFloatingEntitties {
// each of these needs a parent. They cannot float in the model
all d : DataAndLocation | d in Report.dataLocation
all fc : FiscalCode | fc in Citizen.fiscalCode
all lp : LicensePlate | lp in Report.licensePlate
}

fact citizenMustBeActiveInOrderToReport {
no c: Citizen | c.status = Created and c.fiscalCode in Report.fiscalCode
}

// statistics
abstract sig Statistic {}
one sig StatBase extends Statistic {accessibility: EndUser} 
one sig  StatAdvanced extends Statistic {
accessibility: some PA
}

fact defineAccessibilityContrainst {
all u : User | u in EndUser.composedBy
all u : PA | u in StatAdvanced.accessibility
}

pred showBasicService {
#Report = 4
#Violation = 1
#Citizen = 3
}

run showBasicService for 6
