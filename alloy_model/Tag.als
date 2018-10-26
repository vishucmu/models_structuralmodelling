/*
 * 	17-651 | Group Project | Team 9
 */

open Signature
open Invariant
open Privacy

/*
*	Add a tag. Tagger, taggee, and content associated
*	are all contained in the Tag signature
*/
pred addTag[n, n' : Nicebook, t : Tag] {
	// a comment can not be tagged
	t.content not in Comment
	// u1, u2 are friends (u1 is tagger, u2 is taggee)
	t.taggee in t.tagger.friends
	// u1, u2 are users of Nicebook
	t.taggee in n.users
	t.tagger in n.users
	// a user can not tag him/herself
	t.tagger != t.taggee
	// the content c is in Nicebook n
	t.content in n.contents
	// the content associated must be uploaded by taggee or its friend
	t.content.uploadedBy in t.taggee + t.taggee.friends
	// tagger must able to view the content 
	contentCanView[n, t.tagger, t.content]
	// no duplicate tags
	no t' : n.tags | t != t'
	
	// users and contents remain unchanged
	n'.users = n.users
	n'.contents = n.contents
	// add the tag
	n'.walls = n.walls + t.taggee->t.content
	n'.tags = n.tags + t
}

/*
*	Remove a tag. Tagger, taggee, and content associated
*	are all contained in the Tag signature
*/
pred removeTag[n, n' : Nicebook, t : Tag, u : User]{
	// user has right to remove the tag
	u in t.tagger + t.taggee + t.content.uploadedBy
	// the tag is in Nicebook n
	t in n.tags
	// a user can not tag him/herself
	t.tagger != t.taggee
	// a comment can not be tagged
	t.content not in Comment
	// u1, u2 are users of Nicebook
	t.tagger in n.users 
	t.taggee in n.users
	// the content c is in Nicebook n
	t.content in n.contents
	// users, walls remain unchanged
	n'.users = n.users
	n'.walls = n.walls
	n'.contents = n.contents
	// remove the tag
	n'.tags = n.tags - t
}

// Check for addtag operation
assert AddTagCheck {
	all n, n' : Nicebook, t : Tag | 
		(nicebookInvariant[n] and tagInvariant[n, t] and addTag[n, n', t]) implies nicebookInvariant[n']
} 

// Check for removetag operation
assert RemoveTagCheck {
	all n, n' : Nicebook, t : Tag, u : User | 
		(userInvariant[n, u] and nicebookInvariant[n] and tagInvariant[n, t] and removeTag[n,n', t,u]) implies nicebookInvariant[n']
}

run runTag {
	all n : Nicebook | nicebookInvariant[n]
	some n, n' : Nicebook, t : Tag | 
		nicebookInvariant[n] and tagInvariant[n, t] and addTag[n, n', t] and nicebookInvariant[n']
	some n, n' : Nicebook, t : Tag, u : User | 
		userInvariant[n, u] and nicebookInvariant[n] and tagInvariant[n, t]
			and removeTag[n,n', t,u] and nicebookInvariant[n']
} for 10

check AddTagCheck for 10
check RemoveTagCheck for 10

