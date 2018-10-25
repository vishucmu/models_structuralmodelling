/*
 * 	17-651 | Group Project | Team 9
 */

open Privacy

// User u uploads content c with privacy level p
// c is before upload, c' is after upload
pred upload[n, n' : Nicebook, u : User, c : Content, p : PrivacyLevel]
{
	// Percondition
	// u is a user of Nicebook n
	u in n.users
	// the content is not already in Nicebook n
	c not in n.contents
	// the content is uploaded by user u
	c.uploadedBy = u
	// no tags initially
	c not in n.tags.content
	// privacy level of content is p
	c.privacy = p
	// Postcondition
	// users, walls, and tags remain unchanged
	n'.users = n.users
	n'.walls = n.walls
	n'.tags = n.tags
	// the content c is added in n’
	// if c is a note, the photos it contains will be uploaded together
	c in Note implies n'.contents = n.contents + c + c.contain 
		else n'.contents = n.contents + c
	// no comment attached to c initially
	all com : n.contents | 
		com in Comment implies c not in com.attachedTo
}

// User u removes content c
pred remove[n, n' : Nicebook, u : User, c : Content] 
{
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// the content c is uploaded by user u
	c.uploadedBy = u
	// the content c is in Nicebook n
	c in n.contents
	// comments can not be removed
	c not in Comment
	// if c is a photo and is contained by a note
	// it cannot be removed independly
	not (c in Photo and (some c' : n.contents | c in c'.contain))
	// Postcondition
	// users and tags remain unchanged
	n'.users = n.users
	n'.tags = n.tags
	// remove content c from contents
	n'.contents = n.contents - c - (^attachedTo).c
	all u' : n.users | n'.walls[u'] = n.walls[u'] - c
	n'.tags = n.tags - content.c
}

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
	// the content c is in Nicebook n
	t.content in n.contents
	// the content associated must be uploaded by taggee or its friend
	t.content.uploadedBy in t.taggee + t.taggee.friends
	// tagger must able to view the content 
	contentCanView[n, t.tagger, t.content]
	// no duplicate tags
	no t' : Tag | t = t'
	
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
	// remove the tag
	n'.tags = n.tags - t
}

/*
*	User u add comment to content c
*/

pred addComment[n, n' : Nicebook, u: User, c : Content, com, com' : Comment] {
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// c is a content of Nicebook n
	c in n.contents
	// c can be viewd on someone's wall
	some c' : n.contents | some u' : n.walls.c' | c' in onWallContent[n, c] and 
		contentOnWallCanView[n, u, u', c'] and privacyFollow[u, u', u'.privacyComment]
	// comment com is not attached to any content
	no com.attachedTo
	// comment com is uploaded by user u
	u = com.uploadedBy
	// comment com has no privacy level
	no com.privacy	
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
	no com'.privacy
	com'.attachedTo = c
}

// Check for upload operation
assert UploadCheck {
	all n, n' : Nicebook, c : Content, u : User, p : PrivacyLevel | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and upload[n,n',u,c,p]) implies (nicebookInvariant[n'])
}

// Check for remove operation
assert RemoveCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and remove[n,n',u,c]) implies (nicebookInvariant[n'])
}

// Check for publish operation
assert PublishCheck {
	all n, n' : Nicebook, c : Content, u1, u2 : User, p : PrivacyLevel | 
		(userInvariant[u1] and userInvariant[u2] and contentInvariant[c] and nicebookInvariant[n] 
			and publish[n,n',c,u1,u2,p]) implies (nicebookInvariant[n'])
}

// Check for unpublish operation
assert UnpublishCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and unpublish[n,n',c,u]) implies (nicebookInvariant[n'])
}

// Check for addtag operation
assert AddTagCheck {
	all n, n' : Nicebook, t : Tag | 
		(nicebookInvariant[n] and tagInvariant[n, t] and addTag[n,n',t]) implies (nicebookInvariant[n'])
}

// Check for removetag operation
assert RemoveTagCheck {
	all n, n' : Nicebook, t : Tag, u : User | 
		(userInvariant[u] and nicebookInvariant[n] and addTag[n,n',t]
			and removeTag[n,n', t,u]) implies (nicebookInvariant[n'])
}

// Check for addcomment operation
assert AddCommentCheck {
	all n, n' : Nicebook, u: User, c : Content, com, com' : Comment | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] and
			contentInvariant[com] and contentInvariant[com'] and 
				addComment[n, n', u, c , com, com'])
					implies (nicebookInvariant[n'])
}

fun viewable[n : Nicebook, u : User] : set Content {
	// If content c is uploaded by user u, u can view c
	{c : n.contents | u = c.uploadedBy or contentCanView[n, u, c]}	
}

// the assertion NoPrivacyViolation
assert NoPrivacyViolation {
	all n: Nicebook, u : User | all c : viewable[n, u] |
		privacyFollow[u, c.uploadedBy, c.privacy]
}

check UploadCheck for 10
check RemoveCheck for 10
check PublishCheck for 10
check UnpublishCheck for 10
check AddTagCheck for 10
check RemoveTagCheck for 10
check AddCommentCheck for 10
