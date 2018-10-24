/*
 * 	17-651 | Group Project | Team 9
 */

// the signature of our social network 
sig Nicebook {
	// set of users in the social network
	users : set User,
	// the unique walls for each user
	walls : User -> set Content,
	// set of contents in the social network
	contents : set Content
}

sig User {
	// set of friends for a user
	friends : set User,
	// user's privacy setting of who can view his/her content
	privacyView: one PrivacyLevel,
	// user's privacy setting of who can add comment to his/her content
	privacyComment: one PrivacyLevel
}

abstract sig Content {
	// the user that upload this content
	uploadedBy : one User,
	// the User to User relationship of this content
	// the left User is the one who tagged this content
	// the right User is the one who got tagged by another user
	tags : User -> one User,
	removeTags : User -> one User,
	// the privacy level of this content
	privacy : lone PrivacyLevel
}

/*
 *  	a content must be one of the following three types:
* 	a photo, a note, or a comment
 */

sig Photo extends Content {}

sig Note extends Content {
	// a note may contain one or more photos
	contain : set Photo
}

sig Comment extends Content {
	// a comment can attach to any types of content
	attachedTo: lone Content
}

/*
 * 	Every content must have a privacy level, and the privacy
*	level must be one of the following four types:
*	only me, friends, friends of friends, and everyone
 */

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
	// Every content in the wall should exist in the Nicebook
	all u : User | all c : n.walls[u] | c in n.contents and c not in Comment
}

pred userInvariant[u : User] {
	// Friendship is a symmetric relation
	all u' : User | u in u'.friends iff u' in u.friends
	// A user cannot be its own friend.
	not u in u.friends
}

pred contentInvariant[c : Content] {
	// Tags should only exist in notes and photos
	c in Comment implies (no c.tags and c not in c.^attachedTo)
	// A user can only tag his/her friends
	all u : User | all u' : c.tags[u] | u in u'.friends
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

// In Nicebook n, whether user u can view wall w
pred wallCanView[n : Nicebook, u, u' : User] {
	privacyCanView[u, u', u'.privacyView]
}

// Whether user u can view content c
pred contentCanView[u : User, c : Content] {
	privacyCanView[u, c.uploadedBy, c.privacy]
}

// Whether user u can view comment c
pred commentCanView[u : User, c : Comment] {
	// u can view c
	contentCanView[u, c]
	// u can view the content c attached to recursively
	all c' : c.^attachedTo | contentCanView[u, c']
}

// Part by Tianli
// addComment
pred addComment[n, n' : Nicebook, u: User, c : Content, com, com' : Comment, p : PrivacyLevel] {
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// c is a content of Nicebook n
	c in n.contents
	// Comment com is not attached to any content
	no com.attachedTo
	// In Nicebook n, user u can view content c
	c in viewable[n, u]
	// Comment com is uploaded by user u
	u = com.uploadedBy
	// Comment com has no tags / remove tags
	no com.tags
	no com.removeTags
	// Comment com has privacy level p
	com.privacy = p
	// Postcondition
	// Users and walls remained
	n'.users = n.users
	n'.walls = n.walls
	// Add comment com' to new Nicebook's content list, remote origin com
	n'.contents = n.contents - com + com'
	// Except for the content the comment attached to, every attribute remains
	com'.uploadedBy = u
	no com'.tags
	no com'.removeTags
	com'.privacy = com.privacy
	com'.attachedTo = c
	com'.privacy = p
}

// Part by Tianli
// viewable
fun viewable[n : Nicebook, u : User] : set Content {
	// If content c is uploaded by user u, u can view c
	{c : n.contents | c.uploadedBy = u or (
		// If on a wall that user u can view...
		some u' : n.users | let w = n.walls[u'] | wallCanView[n, u, w] and (
			// If c is published on the wall, u can view c under privacy setting
			(c in w.publication and contentCanView[u, c]) or 
			// If c is a comment and u can view c under privacy setting
			(c in Comment and commentCanView[u, c] and (
				// If exists a content c' that is published on the wall
				// and c' is attached to by c recursively, u can view c
				some c' : n.contents | 
					c' in c.^attachedTo and c' in w.publication
			))
		)
	)}	
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
	n'.contents = n.contents + c
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
	// Postcondition
	// Frame conditions
	n'.users = n.users
	n'.walls = n.walls
	// Remove c from contents
	n'.contents = n.contents - c
	
}
// Part by Weihsuan ends


// part by yuanzong
pred publish[n, n' : Nicebook, c :Content, u : User, p :PrivacyLevel] {
	// if a content is owned  by the user u, and its a note or photo
	// and it is not already on the user's wall, publish it to the wall
	c not in u.(n.walls)
	(c in (uploadedBy.u)) and (c not in Comment)
		implies n'.walls = n.walls + (u -> c) 
	// if a content is owned  by the user's friend, and its a note or photo
	// and it is not already on the friend's wall, publish it to the wall
	(c in (uploadedBy.(u.friends))) and (c not in Comment)
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
	(c in u.(n.walls) and wallCanView[n, u, w] and contentCanView[u, c]) 
		implies n'.walls = n.walls + (u -> c)
	// users set won't change
	n'.users = n.users
	// contents in the Nicebook won't change
	n'.contents = n.contents	
}

//Part by Vishwas

pred addTag[n,n' : Nicebook, c, c' : Content, u1, u2 : User] {
	//a user can tag another user on a photo, note - however the user can not be tagged on a //comment, also the content get published to a user who is tagged on the note or photo
	all w,w' : u2.(n.walls) | (c not in Comment)
	            implies 
	            (u1->u2) in c.tags and w'.publication =  w.publication + c and n'.walls = n.walls + u2->w'

	//the privacy level should not change even in case a new user is tagged on the note or photo
	c'.privacy = c.privacy
	//there are no changes to formal structure of nicebook
	n'.users = n.users
	n'.walls = n.walls
	n'.contents = n.contents
}

pred removeTag[n,n' : Nicebook, c: Content, u1,u2 : User]{
//a user can remove herself or the content publisher can remove tag from the published content //u1 is the publisher of content, u2 is the user that was tagged
	all w,w' : u2.(n.walls) | (c not in Comment) and c.uploadedBy = u1
		implies 
		((u1->u2) in c.removeTags and (u2->u2) in c.removeTags) and w'.publication = w.publication - c 
		and n'.walls = n.walls + u2 -> w' //a user can be removed by the publisher of content or the user himself
}

