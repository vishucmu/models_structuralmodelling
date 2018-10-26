/*
 * 	17-651 | Group Project | Group 9
 *      verified version of privacy utilities
 */

open Signature
open Invariant

// Check whether u has permission to the content/wall of u'
// with a privacy level of p
pred privacyFollow[u, u' : User, p : PrivacyLevel] {
	// everyone
	p = Everyone or 
	// friends of friends
	(p = FriendsOfFriends and u in u' + u'.friends + u'.friends.friends) or
	// friends
	(p = Friends and u in u' + u'.friends) or
	// only me
	(p = OnlyMe and u = u')
}

// Check whether user u can view content c
// directly on the wall of u'
pred contentOnWallCanView[n : Nicebook, u, u' : User, c : Content] {
	// content c should be on the wall of u'
	c in n.walls[u']
	// follow the privacy level of content c
	privacyFollow[u, c.uploadedBy, c.privacy]
	// if content is not uploaded by u', then follow
	// the view privacy level of u'
	u' != c.uploadedBy implies privacyFollow[u, u', u'.privacyView]
}

// Find a set of contents on wall that the current content belongs to
fun onWallContent[n : Nicebook, c : Content] : set Content {
	// Find content c' in some user's wall that
	{c' : n.contents | some u : n.users | c' in n.walls[u] and (
		// c is c'
		c' = c or
		// c is a comment and c is attached to c' recursively
		(c in Comment and (c' in c.^attachedTo or 
			// c' is a note and c is attached to a photo c'' recusively
			// and c'' is contained by c'
			(c' in Note and (some c'' : n.contents | 
				c'' in Photo and c'' in c'.contain and c'' in c.^attachedTo)))) or
		// c is a photo and c' is a note containing c
		(c in Photo and c' in Note and c in c'.contain)
	)}
}

// Check whether user u can view content c
pred contentCanView[n : Nicebook, u : User, c : Content] {
	some c' : n.contents | some u' : n.walls.c' | 
		c' in onWallContent[n, c] and contentOnWallCanView[n, u, u', c']
}

fun viewable[n : Nicebook, u : User] : set Content {
	// If content c is uploaded by user u, u can view c
	{c : n.contents | u = c.uploadedBy or contentCanView[n, u, c]}	
}

// the assertion NoPrivacyViolation
assert NoPrivacyViolation {
	all n: Nicebook | all u : n.users | all c : viewable[n, u] |
		nicebookInvariant[n] implies privacyFollow[u, c.uploadedBy, c.privacy]
}
check NoPrivacyViolation 


