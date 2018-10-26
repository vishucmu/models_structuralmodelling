/*
 * 	17-651 | Group Project | Team 9
 */

open Signature

pred nicebookInvariant[n : Nicebook] {
	// no user can have wall without being Nicebook's user
	no u : User | u not in n.users and (some c : Content | c = n.walls[u])
	// every content in the wall should exist in the Nicebook
	// and it can not be a comment (comment can not exist without
	// attach to some content)
	all u : n.users | all c : n.walls[u] | c in n.contents
		and c not in Comment and c.uploadedBy in u + u.friends
	// all contents of the Nicebook should follow the invariants of contents
	all c : n.contents | contentInvariant[n, c]
	// all users using the wall should follow the invariants of users
	all u : n.users | userInvariant[n, u]
	// all tags of the Nicebook should follow the invariants of tags
	all t : n.tags | tagInvariant[n, t]
}

pred userInvariant[n : Nicebook, u : User] {
	// friendship is a symmetric relation
	all u' : User | u in u'.friends iff u' in u.friends
	// all user's friend should be user of Nicebook
	all u' : u.friends | u' in n.users
	// a user cannot be his/herself's friend.
	u not in u.friends
}

pred contentInvariant[n : Nicebook, c : Content] {
	// comments have no privacy level and can not be attached to itself recursively
	c in Comment implies 
		(c.privacy = Everyone and 
		c not in c.^attachedTo)
	// photos and notes have privacy level
	else (one p : PrivacyLevel | p = c.privacy)
	// notes should follow its invariants
	c in Note implies 
		(all c' : c.contain | 
			c.privacy = c'.privacy and 
			c.uploadedBy = c'.uploadedBy)
	// content should be uploaded by the user of Nicebook
	c.uploadedBy in n.users
	// content uploaded should follow the user invariant
	userInvariant[n, c.uploadedBy]
}

pred tagInvariant[n : Nicebook, t : Tag] {
	// a user can not tag him/herself
	t.tagger != t.taggee
	// both tagger and taggee must be users in Nicebook
	t.tagger in n.users
	t.taggee in n.users
	// both tagger and taggee should follow the user invariant
	userInvariant[n, t.tagger]
	userInvariant[n, t.taggee]
	// the content associated with the tag must be with the Nicebook and follow the content invariant
	contentInvariant[n, t.content]
	t.content in n.contents
	// a user can not tag a comment
	t.content not in Comment
}


