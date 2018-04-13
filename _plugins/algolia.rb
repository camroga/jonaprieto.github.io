module Jekyll
  module Algolia
    module Hooks
      def self.before_indexing_each(record, node, _context)
        return record if node.nil?
        return record unless node.matches?('pre.Agda')

        node.css('a').each do |a|
          a.remove_attribute('href')
          a.remove_attribute('class')
          a.remove_attribute('id')
        end

        record[:html] = node.to_s.strip
        record[:text] = node.content

        record
      end
    end
  end
end
