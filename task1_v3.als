/*
 * 17-651 | Group Project | Team 9
 */

sig Nicebook {
	users : set User,
	walls : users -> Content,
	contents : set Content,
	tags : set Tag
}

sig User {
	friends : set User,
	privacyView: one PrivacyLevel,
	privacyComment: one PrivacyLevel
}

abstract sig Content {
	uploadedBy : one User,
	privacy : one PrivacyLevel
}

sig Photo extends Content {}

sig Note extends Content {
	contain : set Photo
}

sig Comment extends Content {
	attachedTo: lone Content
}

sig Tag {
	tagger : one User,
	taggee : one User,
	content : one Content
}

abstract sig PrivacyLevel {}
// u : User
one sig OnlyMe extends PrivacyLevel {}
// u.friends + u
one sig Friends extends PrivacyLevel {} 
// u.friends.friends + u.friends (u already in this set)
one sig FriendsOfFriends extends PrivacyLevel {}
// User
one sig Everyone extends PrivacyLevel {}

pred nicebookInvariant[n : Nicebook] {
	// No user can have wall without being Nicebook's user
	no u : User | u not in n.users and (some c : Content | c = n.walls[u])
	// Every content in the wall should exist in the Nicebook
	all u : n.users | all c : n.walls[u] | c in n.contents and c not in Comment and c.uploadedBy in u + u.friends
	// All contents of the Nicebook should follow the invariants of contents
	all c : n.contents | contentInvariant[c]
	// All users using the wall should follow the invariants of users
	all u : n.users | userInvariant[u]
	// All tags of the Nicebook should follow the invariants of tags
	all t : n.tags | tagInvariant[n, t]
}

pred userInvariant[u : User] {
	// Friendship is a symmetric relation
	all u' : User | u in u'.friends iff u' in u.friends
	// A user cannot be its own friend.
	not u in u.friends
}

pred contentInvariant[c : Content] {
	// Comments should follow the invariants
	c in Comment implies commentInvariant[c]
	// Photos and notes have privacy level
	one p : PrivacyLevel | p = c.privacy
	// Notes should follow the invariants
	c in Note implies noteInvariant[c]
}

// Comments have no tags, no privacy level and can not be attached to itself recursively
pred commentInvariant[c : Comment] {
	no c.privacy 
	c not in c.^attachedTo
}

pred tagInvariant[n : Nicebook, t : Tag] {
	t.tagger != t.taggee
	t.tagger in n.users
	t.taggee in n.users
	t.content in n.contents
	t.content not in Comment
}

// Notes' privacy level should be same as all its photos (assumption)
pred noteInvariant[c : Note] {
	all c' : c.contain | c.privacy = c'.privacy
}

// Part of Tianli
// Whether u has permission to content/wall of u' will a p privacy level
pred privacyFollow[u, u' : User, p : PrivacyLevel] {
	// Everyone
	p = Everyone or 
	// Friends of friends
	(p = FriendsOfFriends and u in u' + u'.friends + u'.friends.friends) or
	// Friends
	(p = Friends and u in u' + u'.friends) or
	// Only me
	(p = OnlyMe and u = u')
}

// Whether user u can view content c directly on the wall of u'
pred contentOnWallCanView[n : Nicebook, u, u' : User, c : Content] {
	// Content c should be on the wall of u'
	c in n.walls[u']
	// If u = u', all content can be viewed on his/her wall
	u = u' or (
		// If content is uploaded by u', then follow the privacy level of content
		(u' = c.uploadedBy implies privacyFollow[u, u', c.privacy]) and
		// If content is not uploaded sy u', then follow the view privacy level of u'
		(u' != c.uploadedBy implies privacyFollow[u, u', u'.privacyView])
	)
}

// find a set of contents on wall that the current belongs to
fun onWallContent[n : Nicebook, c : Content] : set Content {
	{c' : n.contents | some u : n.users | c' in n.walls[u] and (
		c' = c or
		(c in Comment and c' in c.^attachedTo) or
		(c in Photo and c' in Note and c in c'.contain)
	)}
}

// Whether user u can view content c
pred contentCanView[n : Nicebook, u : User, c : Content] {
	some c' : n.contents | some u' : n.walls.c' | c' in onWallContent[n, c] and contentOnWallCanView[n, u, u', c']
}

// Part by Tianli
// addComment
pred addComment[n, n' : Nicebook, u: User, c : Content, com, com' : Comment] {
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// c is a content of Nicebook n
	c in n.contents
	// c can be viewd on someone's wall
	some c' : n.contents | some u' : n.walls.c' | c' in onWallContent[n, c] and 
		contentOnWallCanView[n, u, u', c'] and privacyFollow[u, u', u'.privacyComment]
	// Comment com is not attached to any content
	no com.attachedTo
	// Comment com is uploaded by user u
	u = com.uploadedBy
	// Comment com has no privacy level
	no com.privacy	
	// Postcondition
	// Users and walls remained
	n'.users = n.users
	n'.walls = n.walls
	n'.tags = n.tags
	// Add comment com' to new Nicebook's content list, remote origin com
	n'.contents = n.contents - com + com'
	// Except for the content the comment attached to, every attribute remains
	com'.uploadedBy = u
	no com'.privacy
	com'.attachedTo = c
}

// Part by Tianli
// viewable
fun viewable[n : Nicebook, u : User] : set Content {
	// If content c is uploaded by user u, u can view c
	{c : n.contents | u = c.uploadedBy or contentCanView[n, u, c]}	
}

/*
  * Part by Wei-Hsuan :
  * 1. upload
  * 2. remove
  */

// User u uploads content c with privacy level p
// c is before upload, c' is after upload
pred upload[n, n' : Nicebook, u : User, c : Content, p : PrivacyLevel]
{
	// Percondition
	// u is a user of Nicebook n
	u in n.users
	// c is not in n
	c not in n.contents
	// c is uploaded by u
	c.uploadedBy = u
	// No tags initially
	c not in n.tags.content
	// Privacy level of content is p
	c.privacy = p
	// Postcondition
	// Frame conditions
	n'.users = n.users
	n'.walls = n.walls
	n'.tags = n.tags
	// c is in n’
	c in Note implies n'.contents = n.contents + c + c.contain 
	(c in Comment + Photo) implies n'.contents = n.contents + c
	// No comment attached to c initially
	all com : n.contents | 
		com in Comment implies c not in com.attachedTo
}

// User u removes content c
pred remove[n, n' : Nicebook, u : User, c : Content] 
{
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// c is uploaded by u
	c.uploadedBy = u
	// c is in n
	c in n.contents
	c not in Comment
	// Postcondition
	// Frame conditions
	n'.users = n.users
	n'.tags = n.tags
	// Remove c from contents
	n'.contents = n.contents - c - (^attachedTo).c
	all u' : n.users | n'.walls[u'] = n.walls[u'] - c
	n'.tags = n.tags - {t : n.tags | t.content = c}
}

// Returns all comments attached to content c
fun allComments[c : Content] : set Comment
{
	{com : Comment |
		c in com.^attachedTo
	}
}
// Part by Weihsuan ends

// part by yuanzong
pred publish[n, n' : Nicebook, c : Content, u, u' : User, p : PrivacyLevel] {
	// Precondition
	u in n.users
	u' in n.users
	// if a content is owned by the user u, and its a note or photo
	// and it is not already on the user's wall, publish it to the wall
	c not in n.walls[u']
	c not in Comment
	// The publisher can view the content
	contentCanView[n, u, c] or u = c.uploadedBy
	// The content is uploaded by the wall's owner or his/her friend
	c.uploadedBy in u' + u'.friends
	// If c is newly uplaoded, c has no comment or tag
	c not in n.contents implies (
		(no com : n.contents | com in Comment and c in com.^attachedTo) and
		c not in n.tags.content and
		c.privacy = p
	)
	// Postcondition
	n'.walls = n.walls + u'->c
	n'.contents = n.contents + c
	n'.users = n.users
	n'.tags = n.tags
}

pred unpublish[n, n' : Nicebook, c : Content, u : User] {
	// if c is in the user u's wall and , unpublish it
	c in n.walls[u]
	c not in Comment
	n'.walls = n.walls - (u -> c)
	// users set won't change
	n'.users = n.users
	// contents in the Nicebook won't change
	n'.contents = n.contents
	n'.tags = n.tags	
}

//Part by Vishwas
pred addTag[n, n' : Nicebook, t : Tag] {
	// c is not a comment
	t.content not in Comment
	// u1, u2 are friends
	t.taggee in t.tagger.friends
	// u1, u2 are users of Nicebook
	t.taggee in n.users
	t.tagger in n.users
	// c is content of n
	t.content in n.contents
	t.content.uploadedBy in t.taggee + t.taggee.friends
	contentCanView[n, t.tagger, t.content]

	no t' : Tag | t = t'

	n'.users = n.users
	n'.contents = n.contents
	n'.walls = n.walls + t.taggee->t.content
	n'.tags = n.tags + t
}

// remover removing u1->u2 from c
pred removeTag[n, n' : Nicebook, t : Tag, u : User]{
	// remover is legal
	u in t.tagger + t.taggee + t.content.uploadedBy

	t in n.tags
	// c is not a comment
	t.content not in Comment
	// u1, u2 are users of Nicebook
	t.tagger in n.users 
	t.taggee in n.users
	// c is content of n
	t.content in n.contents

	n'.users = n.users
	n'.walls = n.walls
	n'.tags = n.tags
}

assert UploadCheck {
	all n, n' : Nicebook, c : Content, u : User, p : PrivacyLevel | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and upload[n,n',u,c,p]) implies (nicebookInvariant[n'])
}

assert RemoveCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and remove[n,n',u,c]) implies (nicebookInvariant[n'])
}

assert PublishCheck {
	all n, n' : Nicebook, c : Content, u1, u2 : User, p : PrivacyLevel | 
		(userInvariant[u1] and userInvariant[u2] and contentInvariant[c] and nicebookInvariant[n] 
			and publish[n,n',c,u1,u2,p]) implies (nicebookInvariant[n'])
}

assert UnpublishCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and unpublish[n,n',c,u]) implies (nicebookInvariant[n'])
}

assert AddTagCheck {
	all n, n' : Nicebook, t : Tag | 
		(nicebookInvariant[n] and tagInvariant[n, t] and addTag[n,n',t]) implies (nicebookInvariant[n'])
}

assert RemoveTagCheck {
	all n, n' : Nicebook, t : Tag, u : User | 
		(userInvariant[u] and nicebookInvariant[n] and addTag[n,n',t]
			and removeTag[n,n', t,u]) implies (nicebookInvariant[n'])
}

assert AddCommentCheck {
	all n, n' : Nicebook, u: User, c : Content, com, com' : Comment | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] and
			contentInvariant[com] and contentInvariant[com'] and 
				addComment[n, n', u, c , com, com'])
					implies (nicebookInvariant[n'])
}

assert NoPrivacyViolation {
	all n: Nicebook, u : User | all c : viewable[n, u] |
		privacyCanView[u, c.uploadedBy, c.privacy]
}

check UploadCheck for 10
check RemoveCheck for 10
check PublishCheck for 10
check UnpublishCheck for 10
check AddTagCheck for 10
check RemoveTagCheck for 10
check AddCommentCheck for 10

