/*
 * 	17-651 | Group Project | Group 9
 *      All signatures of Nicebook
 */

// The signature of our social network 
sig Nicebook {
	// set of users in the social network
	users : set User,
	// the unique walls for each user
	walls : users -> Content,
	// set of contents in the social network
	contents : set Content,
	// set of tags
	tags : set Tag
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
	// the privacy level of this content
	privacy : one PrivacyLevel
}

/*
 *  	A content must be one of the following three types:
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
 *  	The signature that represents a tag relation, it contains tagger, 
* 	taggee, and content
*/

sig Tag {
	// the user who perform the tag action
	tagger : one User,
	// the user who got tagged
	taggee : one User,
	// the content that is associated with the tag
	content : one Content
}

/*
 * 	Every content must have a privacy level, and the privacy
*	level must be one of the following four types:
*	only me, friends, friends of friends, and everyone
*
*	Each user must have a privacy level as well
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

