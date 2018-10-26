/*
 * 	17-651 | Group Project | Team 9
 */

open Signature
open Invariant
open Privacy

/*
*	User u add comment to content c
*/

pred addComment[n, n' : Nicebook, u: User, c : Content, com, com' : Comment] {
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// c is a content of Nicebook n
	c in n.contents
	// comment is not attached to itself
	com != c
	// new comment is not an existing one
	com' not in n.contents
	// c can be viewd on someone's wall
	some c' : n.contents | some u' : n.walls.c' | c' in onWallContent[n, c] and 
		contentOnWallCanView[n, u, u', c'] and privacyFollow[u, u', u'.privacyComment]
	// comment com is not attached to any content
	no com.attachedTo
	// comment com is uploaded by user u
	u = com.uploadedBy
	// comment com has privacy level Everyone
	com.privacy = Everyone
	// no comment attached to the current comment
	all c'' : n.contents | c'' in Comment implies com != c''.attachedTo
	// Postcondition
	// users, walls, and tags remain unchanged
	n'.users = n.users
	n'.walls = n.walls
	n'.tags = n.tags
	// add comment com' to new Nicebook's content list, remove origin com
	n'.contents = n.contents - com + com'
	// except for the content the comment is attached to
	// every attribute remains
	com'.uploadedBy = u
	com'.privacy = Everyone
	com'.attachedTo = c
}

// Check for addcomment operation
assert AddCommentCheck {
	all n, n' : Nicebook, u: User, c : Content, com, com' : Comment | (addComment[n, n', u, c , com, com'] and
		userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] and 
			contentInvariant[n, com] and contentInvariant[n, com']) implies nicebookInvariant[n']
}

run runComment {
	all n : Nicebook | nicebookInvariant[n]
	some n, n' : Nicebook, u: User, c : Content, com, com' : Comment | addComment[n, n', u, c , com, com'] and
		userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] and nicebookInvariant[n'] and
			contentInvariant[n, com] and contentInvariant[n, com']
} for 10

check AddCommentCheck for 10
