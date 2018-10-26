/*
 * 	17-651 | Group Project | Group 9
 *      publish/unpublish content
 */

open Signature
open Invariant
open Privacy

/*
*	User u publish content c on the wall of u'
*/
pred publish[n, n' : Nicebook, c : Content, u, u' : User, p : PrivacyLevel] {
	// Precondition
	// both u and u' are users in Nicebook n
	u in n.users
	u' in n.users
	// the content c is not already on the wall 
	c not in n.walls[u']
	// a comment can not be published directly
	c not in Comment
	// the publisher must able to view the content
	contentCanView[n, u, c] or u = c.uploadedBy
	// the content is uploaded by the wall's owner or his/her friend
	c.uploadedBy in u' + u'.friends
	// if c haven't been uplaoded yet, c has no comment or tag
	c not in n.contents implies (
		(no com : n.contents | com in Comment and c in com.^attachedTo) and
		c not in n.tags.content and
		c.privacy = p
	)
	// Postcondition
	// publish the content on the wall
	n'.walls = n.walls + u'->c
	// if content c has not been uploaded before publish, upload it
	n'.contents = n.contents + c
	// users and tags remain unchanged
	n'.users = n.users
	n'.tags = n.tags
}

/*
*	User u publish content c from his/her own wall
*/
pred unpublish[n, n' : Nicebook, c : Content, u : User] {
	// the content c must be on the user's wall
	c in n.walls[u]
	// comment can not be directly unpublished
	c not in Comment
	// unpublish content c from user's wall
	n'.walls = n.walls - (u -> c)
	// users, contents, tags remain unchanged
	n'.users = n.users
	n'.contents = n.contents
	n'.tags = n.tags	
}

// Check for publish operation
assert PublishCheck {
	all n, n' : Nicebook, c : Content, u, u' : User, p : PrivacyLevel | 
		(userInvariant[n, u] and userInvariant[n, u'] and contentInvariant[n, c] and 
			nicebookInvariant[n] and publish[n, n', c, u, u', p]) implies 
				nicebookInvariant[n']
}

// Check for unpublish operation
assert UnpublishCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] 
			and unpublish[n, n', c, u]) implies nicebookInvariant[n']
}

run runPublish {
	all n : Nicebook | nicebookInvariant[n]
	some n, n' : Nicebook, c : Content, u, u' : User, p : PrivacyLevel | 
		userInvariant[n, u] and userInvariant[n, u'] and 
			contentInvariant[n, c] and nicebookInvariant[n] and 
			publish[n, n', c, u, u', p] and nicebookInvariant[n']
	some n, n' : Nicebook, c : Content, u : User | 
		userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] 
			and unpublish[n, n', c, u] and nicebookInvariant[n']
} for 12 but exactly 3 Nicebook

check PublishCheck for 12 but exactly 2 Nicebook
check UnpublishCheck for 12 but exactly 2 Nicebook

