/*
 * 17-651 | Group Project | Team 9
 */

sig Nicebook {
	users : set User,
	walls : users -> Content,
	contents : set Content
}

sig User {
	friends : set User,
	privacyView: one PrivacyLevel,
	privacyComment: one PrivacyLevel
}

abstract sig Content {
	uploadedBy : one User,
	tags : User -> one User,
	privacy : one PrivacyLevel
}

sig Photo extends Content {}

sig Note extends Content {
	contain : set Photo
}

sig Comment extends Content {
	attachedTo: lone Content
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
	all u : User | all c : n.walls[u] | c in n.contents and c not in Comment
	// All contents of the Nicebook should follow the invariants of contents
	all c : n.contents | contentInvariant[c]
	// All users using the wall should follow the invariants of users
	all u : User | userInvariant[u]
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
	// A user can only tag his/her friends
	all u : User | all u' : c.tags[u] | u in u'.friends and u != u'
}

// Comments have no tags, no privacy level and can not be attached to itself recursively
pred commentInvariant[c : Comment] {
	no c.tags 
	no c.privacy 
	c not in c.^attachedTo
}

// Notes' privacy level should be same as all its photos (assumption)
pred noteInvariant[c : Note] {
	all c' : c.contain | c.privacy = c'.privacy
}

// Part of Tianli
// Whether u has permission to content/wall of u' will a p privacy level
pred privacyCanView[u, u' : User, p : PrivacyLevel] {
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
	// If u = u', all contentc can be viewed on his/her wall
	u = u' or (
		// If content is uploaded by u', then follow the privacy level of content
		(u' = c.uploadedBy implies privacyCanView[u, u', c.privacy]) and
		// If content is not uploaded sy u', then follow the view privacy level of u'
		(u' != c.uploadedBy implies privacyCanView[u, u', u'.privacyView])
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
	contentCanView[n, u, c]
	// Comment com is not attached to any content
	no com.attachedTo
	// Comment com is uploaded by user u
	u = com.uploadedBy
	// Comment com has no tags / privacy level
	no com.tags
	no com'.privacy
	// Postcondition
	// Users and walls remained
	n'.users = n.users
	n'.walls = n.walls
	// Add comment com' to new Nicebook's content list, remote origin com
	n'.contents = n.contents - com + com'
	// Except for the content the comment attached to, every attribute remains
	com'.uploadedBy = u
	no com'.tags
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
	no c.tags
	// Privacy level of content is p
	c.privacy = p
	// Postcondition
	// Frame conditions
	n'.users = n.users
	n'.walls = n.walls
	// c is in n’
	c in Note implies n'.contents = n.contents + c + c.contain 
	(c in Comment or c in Note) implies n'.contents = n.contents + c
	// No comment attached to c initially
	all com : n.contents | com in Comment implies c not in com.attachedTo
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
	n'.walls = n.walls
	// Remove c from contents
	n'.contents = n.contents - c
	all u' : User | c in u'.(n.walls) implies n'.walls = n.walls - (u' -> c)
	all c' : Comment | c' in (attachedTo.c) implies n'.contents = n.contents
}


// part by yuanzong
pred publish[n, n' : Nicebook, c :Content, u : User, p :PrivacyLevel] {
	// if a content is owned  by the user u, and its a note or photo
	// and it is not already on the user's wall, publish it to the wall
	c not in u.(n.walls)
	(c in (uploadedBy.u)) and (c not in Comment)
		implies n'.walls = n.walls + (u -> c) 
	// if a content is owned  by the user's friend, and its a note or photo
	// and it is not already on the friend's wall, publish it to the wall
	(c in (uploadedBy.(u.friends))) and (c not in Comment) and (contentOnWallCanView[n, u, u.friends, c])
		implies n'.walls = n.walls + (u -> c)
	// if a content has not been uploaded yet, publish it and add it to the user’s account
	(c not in Comment) and (c not in (uploadedBy.u)) and (c not in (uploadedBy.(u.friends)))
		implies n'.walls = n.walls + (u -> c) and c.privacy = p and c.uploadedBy = u
	n'.users = n.users
	n'.contents = n.contents
	// No tags initially
	no c.tags
	// user's privacy level set to p
	u.privacyView = p
}

pred unpublish[n, n' : Nicebook, c : Content, u : User] {
	// if c is in the user u's wall and , unpublish it
	c in u.(n.walls)
	c not in Comment
	n'.walls = n.walls - (u -> c)
	// users set won't change
	n'.users = n.users
	// contents in the Nicebook won't change
	n'.contents = n.contents	
}

//Part by Vishwas

pred addTag[n, n' : Nicebook, c : Content, u1, u2 : User] {
	// c is not a comment
	c not in Comment
	// u1, u2 are friends
	u2 in u1.friends
	// u1, u2 are users of Nicebook
	u1 in n.users and u2 in n.users
	// c is content of n
	c in n.contents

	// u1 has the permission to view the content
	some u : n.users | contentOnWallCanView[n,u1,u,c] or 
		(some c' : Note | c in c'.contain and contentOnWallCanView[n,u1,u,c'])

	n'.users = n.users
	// add the tag to the c'
	one c' : Content | (c'.tags = c.tags + (u1->u2)) and 
		(c'.privacy = c.privacy) and (c'.uploadedBy = c.uploadedBy) and
			(n'.contents = n.contents - c + c') and
				(all x : n.users | (c not in n.walls[x] implies n'.walls[x] = n.walls[x]) 
					and (c in n.walls[x] implies n'.walls[x] = n.walls[x] - c + c'))
						and publish[n,n',c',u2,c.privacy]
}

// remover removing u1->u2 from c
pred removeTag[n, n' : Nicebook, c : Content, u1, u2, remover: User]{
	// remover is legal
	remover = u1 or remover = u2 or remover = c.uploadedBy

	// c is not a comment
	c not in Comment
	// u1, u2 are friends
	u2 in u1.friends
	// u1, u2 are users of Nicebook
	u1 in n.users and u2 in n.users
	// c is content of n
	c in n.contents

	n'.users = n.users
	// add the tag to the c'
	one c' : Content | (c'.tags = c.tags - (u1->u2)) and 
		(c'.privacy = c.privacy) and (c'.uploadedBy = c.uploadedBy) and
			(n'.contents = n.contents - c + c') and
				(all x : n.users | (c not in n.walls[x] implies n'.walls[x] = n.walls[x]) 
					and (c in n.walls[x] implies n'.walls[x] = n.walls[x] - c + c'))
						and unpublish[n,n',c',u2]
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
	all n, n' : Nicebook, c : Content, u : User, p : PrivacyLevel | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and publish[n,n',c,u,p]) implies (nicebookInvariant[n'])
}

assert UnpublishCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] 
			and unpublish[n,n',c,u]) implies (nicebookInvariant[n'])
}

assert AddTagCheck {
	all n, n' : Nicebook, c : Content, u1, u2 : User | 
		(userInvariant[u1] and userInvariant[u2] and contentInvariant[c] 
			and nicebookInvariant[n] and addTag[n,n',c,u1,u2]) implies (nicebookInvariant[n'])
}

assert RemoveTagCheck {
	all n, n' : Nicebook, c : Content, u1, u2, u : User | 
		(userInvariant[u] and userInvariant[u1] and userInvariant[u2] and
			contentInvariant[c] and nicebookInvariant[n]
			and removeTag[n,n',c,u1,u2,u]) implies (nicebookInvariant[n'])
}

assert AddCommentCheck {
	all n, n' : Nicebook, u: User, c : Content, com, com' : Comment | 
		(userInvariant[u] and contentInvariant[c] and nicebookInvariant[n] and
			contentInvariant[com] and contentInvariant[com'] and 
				addComment[n, n', u, c , com, com'])
					implies (nicebookInvariant[n'])
}

check AddCommentCheck for 10