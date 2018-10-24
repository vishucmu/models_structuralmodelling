/*
 * 17-651 | Group Project | Team 9
 */

/*
 * General Idea: 
 *
 * We don't need to build models of abstract social networks
 * We just take care of our Nicebook
 * That is, for example, the "User" set means all users of Nicebook
 *
 */

// New version begin
sig Nicebook {
	users : set User
	walls : User -> one Wall
	contents : set Content
}

sig User {
	friends : set User
	privacyView: one PrivacyLevel
	privacyComment: one PrivacyLevel
}

Sig Content {
	uploadedBy : one User
	tags : User -> one User
	removeTags :User -> one User
	privacy : one PrivacyLevel
}

sig Photo extends Content {}

sig Note extends Content {
	contain : set Photo
}

sig Comment extends Content {
	attachedTo: one Content
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

sig Wall {
	publication : set Content
}

// New version end

// New version of invariant 
pred nicebookInvariant[n : Nicebook] {
	// Every user has a different wall
	all u, u’ : User | u != u’ implies n.walls[u] != n.walls[u’]
	// Every content in the wall should exist in the Nicebook
	all u : User | all c : n.walls[u].publication | c in n.contents
}

pred userInvariant[u : User] {
	// Friendship is a symmetric relation
	all u’ : User | u in u’.friends iff u’ in u.friends
	// A user cannot be its own friend.
not u in u.friends
}

pred contentInvariant[c : Content] {
	// Tags should only exist in notes and photos
	c in Comment implies no c.tags
	// A user can only tag his/her friends
	all u : User | all u’ : c.tags[u] | u in u’.friends
}

pred wallInvariant[w : Wall] {
	// No comments can directly appear on the wall
	all c : w.publication | not c in Comment
}
// New version of invariant end

/*
  * Part by Wei-Hsuan :
  * 1. upload
  * 2. remove
  */

// User u uploads content c with privacy level p
// c is before upload, c' is after upload
pred upload[n, n' : Nicebook, u : User, c : Content, p : PrivacyLevel]
{
	// Frame conditions
	n'.users = n.users
	n'.walls = n.walls
	// c is not in n
	c not in n.contents
// c is in n’
n’.contents = n.contents + c
	// c is uploaded by u
	c.uploadedBy = u	
	// No tags initially
	no c.tags
	// Privacy level of content is p
	c.privacy = p
	// No comment attached to c initially
	all com : n.contents | c not in com.attachedTo
}

// User u removes content c
pred remove[n, n' : Nicebook, u : User, c : Content] 
{
	// Frame conditions
	n'.users = n.users
	n'.walls = n.walls
// Remove c
	n’contents = n.contents - c
	// c is uploaded by u
	c.uploadedBy = u	
}
// Part by Weihsuan ends


// part by yuanzong
pred publish[n, n’ : Nicebook, c :Content, u : User p :PrivacyLevel] {
	// if a content is owned  by the user u, and its a note or photo
	// and it is not already on the user's wall, publish it to the wall
	all w, w' : u.(n.walls) | (c in (uploadedBy.u)) and (c not in Comment)
		and (c not in w.publication) implies w'.publication = w.publication + c
		and n’.walls = n.walls - (u -> w) + (u -> w’) 
	// if a content is owned  by the user's friend, and its a note or photo
	// and it is not already on the friend's wall, publish it to the wall
	all w, w' : u.(n.walls) | (c in (uploadedBy.(u.friends))) and (c not in Comment)
		and (c not in w.publication) implies w'.publication = w.publication + c
		and n’.walls = n.walls - (u -> w) + (u -> w’)
	// if a content has not been uploaded yet, publish it and add it to the user’s account
	all w, w’ : u.(n.walls) | (c not in Comment) and (c not in w.publication) implies
w’.publication = w.publication + c and n’.walls = n.walls - (u -> w) + (u -> w’)
and c.privacy = p 
	n’.users = n.users
	n’.contents = n.contents
	// No tags initially
	no c.tags
	/ / user’s privacy level set to p
	u.privacyView = p
// No comment attached to c initially
	all com : n.contents | com in Comment implies c not in com.attachedTo
}

pred unpublish[n, n’ : Nicebook, c : Content, u : User] {
	// if c is in the user u's wall and it is an uploaded content, unpublish it
	all w, w' : u.(n.walls) | c in (w.publication)
		implies w'.publication = w.publication - c
		and n’.walls = n.walls - (u -> w) + (u -> w’)
	n’.users = n.users
	n’.contents = n.contents
all com : n.contents | com in Comment implies c not in com.attachedTo	
}

// Part of Tianli
// addComment
pred addComment[n,n’ : Nicebook, u: User,  c : Content, com : Comment] {
	
}

pred contentCanView[n : Nicebook, u : User, c : Content] {

}

// Part of Tianli
// viewable
Func viewable[n : Nicebook, u : User] : set Content {
	
}


//Part by Vishwas

pred addTag[n,n’ : Nicebook, c : Content, u1, u2 : User] {
//a user can tag another user on a photo, note - however the user can not be tagged on a //comment, also the content get published to a user who is tagged on the note or photo
            all w,w’ : u2.(n.walls) and (c not in Comment)    
            (u1->u2) in c.tags and w’.publication =  w.publication + c and n’.walls = n.walls + u2->w’

  //the privacy level should not change even in case a new user is tagged on the note or photo
      c’.privacy = c.privacy
  //there are no changes to frame conditions of nicebook
  n’.users = n.users
  n'.walls = n.walls
  n’.content = n.content
}

pred removeTag[n,n’ : Nicebook, c: Content. u1,u2 : User]{
//a user can remove herself or the content publisher can remove tag from the published content //u1 is the publisher of content, u2 is the user that was tagged
	all w,w’ : u2.(n.walls) and (c not in Comment) and c.uploadedBy = u1
  ((u1->u2) in c.removeTags | (u2->u2) in c.removeTags) 
  and w’.publication = w.publication - c 
  and n’.walls = n.walls + u2 -> w’  //a user can be removed by the publisher of content or the user himself
}


run {
	invariant
} for 3


