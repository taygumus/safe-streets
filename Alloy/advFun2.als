// ACTOR
abstract sig User {}
abstract sig PA extends User {}

one sig Municipality extends PA {}
one sig PoliceOffice extends PA {}

abstract sig TicketStatus {}
one sig IssuedTicket extends TicketStatus {}
one sig NotIssuedTicket extends TicketStatus {}

sig Violation {
ticketStatus: one TicketStatus
}

// in this part of the model we consider the part of the feedback concerned about the ticket being issued or not
sig Feedback {
violation: one Violation,
madeBy: PoliceOffice
}

fact feedbackIssued {
// no more than one feedback for violation
no  f,f'' : Feedback | f != f'' and f.violation = f''.violation
// no feedback with more than one violation
no v,v': Violation, f : Feedback | v != v' and f.violation = v and f.violation = v'
// no issued status without feedback 
no v : Violation | (v.ticketStatus = NotIssuedTicket and v in Feedback.violation) or ( v.ticketStatus = IssuedTicket and v not in Feedback.violation)
}

// statistics
abstract sig Statistic {}
one sig  TIStatistics extends Statistic {
accessibility: some PA
}

fact defineAccessibilityContrainst {
all u : PA | u in TIStatistics.accessibility
}

// generate basic service world
pred showAdvFunction2 {
#Violation = 8
#Feedback = 6
}

run showAdvFunction2 for 8
